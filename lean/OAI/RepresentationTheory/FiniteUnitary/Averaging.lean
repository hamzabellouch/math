import OAI.RepresentationTheory.FiniteUnitary.Coefficients

namespace OAI

namespace CubeShuffle.FiniteConvolution
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]

noncomputable def conv (p q : G → ℝ) (g : G) : ℝ := ∑ h, p h*q (h⁻¹*g)
noncomputable def power (p : G → ℝ) : ℕ → G → ℝ
  | 0 => fun g => if g=1 then 1 else 0
  | n+1 => conv p (power p n)

lemma conv_nonneg {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g) :
    ∀ g, 0 ≤ conv p q g := fun _ => Finset.sum_nonneg (fun h _ => mul_nonneg (hp h) (hq _))

lemma conv_pos_of {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g)
    {a b : G} (ha : 0 < p a) (hb : 0 < q b) : 0 < conv p q (a*b) := by
  apply lt_of_lt_of_le (mul_pos ha hb)
  have h := Finset.single_le_sum (fun g _ => mul_nonneg (hp g) (hq (g⁻¹*(a*b))))
    (Finset.mem_univ a)
  simpa [conv] using h

lemma sum_conv (p q : G → ℝ) : ∑ g, conv p q g=(∑ g,p g)*(∑ g,q g) := by
  unfold conv
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [←Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun _ => rfl)

lemma power_nonneg {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) : ∀ n g, 0 ≤ power p n g := by
  intro n
  induction n with
  | zero => intro g; simp only [power]; split_ifs  <;> norm_num
  | succ n ih => exact conv_nonneg hp ih

lemma sum_power {p : G → ℝ} (hp : ∑ g,p g=1) : ∀ n, ∑ g,power p n g=1 := by
  intro n
  induction n with
  | zero => simp [power]
  | succ n ih => rw [power,sum_conv,hp,ih,one_mul]

lemma power_list_pos {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (l : List G)
    (hl : ∀ g ∈ l, 0 < p g) : 0 < power p l.length l.prod := by
  induction l with
  | nil => simp [power]
  | cons a l ih =>
    simpa only [List.length_cons,List.prod_cons,power] using
      conv_pos_of hp (power_nonneg hp l.length) (hl a (by simp))
        (ih (fun g hg => hl g (by simp [hg])))

lemma power_pos_mono {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (h1 : 0 < p 1)
    {n m : ℕ} (hnm : n ≤ m) {g : G} (hg : 0 < power p n g) : 0 < power p m g := by
  induction m, hnm using Nat.le_induction with
  | base => exact hg
  | succ m _ ih =>
    simpa only [one_mul,power] using conv_pos_of hp (power_nonneg hp m) h1 ih

/-- Finite generation and a positive holding probability produce a genuine
finite-time positive minorant, rather than a spectral-gap assumption. -/
theorem exists_positive_power {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (h1 : 0 < p 1)
    (hgen : Subgroup.closure {g | 0 < p g}=⊤) :
    ∃ n : ℕ, ∀ g, 0 < power p (2^n) g := by
  have hx (g : G) : g ∈ Submonoid.closure {g | 0 < p g} := by
    rw [←Subgroup.closure_toSubmonoid_of_finite,hgen]
    trivial
  choose l hl hprod using fun g => Submonoid.exists_list_of_mem_closure (hx g)
  let n := Finset.univ.sup (fun g => (l g).length)
  refine ⟨n,fun g => ?_⟩
  have hlen : (l g).length ≤ n := Finset.le_sup (f := fun g => (l g).length) (Finset.mem_univ g)
  have hpow : n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hpos := power_list_pos hp (l g) (hl g)
  rw [hprod g] at hpos
  exact power_pos_mono hp h1 (hlen.trans hpow) hpos

structure Minorant (p : G → ℝ) where
  exponent : ℕ
  mass : ℝ
  mass_pos : 0 < mass
  mass_le_one : mass ≤ 1
  lower : ∀ g, mass/(Fintype.card G:ℝ) ≤ power p (2^exponent) g

noncomputable def minorant {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hsum : ∑ g,p g=1)
    (h1 : 0 < p 1) (hgen : Subgroup.closure {g | 0 < p g}=⊤) : Minorant p := by
  let n := Classical.choose (exists_positive_power hp h1 hgen)
  have hn := Classical.choose_spec (exists_positive_power hp h1 hgen)
  let a := Finset.univ.inf' Finset.univ_nonempty (power p (2^n))
  have ha : 0 < a := (Finset.lt_inf'_iff _).mpr (fun g _ => hn g)
  have hag (g : G) : a ≤ power p (2^n) g := Finset.inf'_le _ (Finset.mem_univ g)
  have hN : (0:ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hsum' := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hag g)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sum_power hsum] at hsum'
  refine ⟨n,(Fintype.card G:ℝ)*a,mul_pos hN ha,hsum',fun g => ?_⟩
  have he : (Fintype.card G:ℝ)*a/(Fintype.card G:ℝ)=a := by field_simp
  rw [he]
  exact hag g

end CubeShuffle.FiniteConvolution
namespace CubeShuffle.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

omit [Fintype G] in
@[simp] lemma continuousRepresentation_apply (ρ : Representation ℂ G V) (g : G) (v : V) :
    continuousRepresentation ρ g v=ρ g v := rfl

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_norm (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v : V) :
    ‖ρ g v‖=‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),hρ,norm_eq_sqrt_re_inner (𝕜 := ℂ)]

omit [Fintype G] in
lemma continuousRepresentation_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    ‖continuousRepresentation ρ g‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [continuousRepresentation_apply,unitary_norm ρ hρ,one_mul,le_refl]

omit [Fintype G] in
lemma continuousRepresentation_adjoint (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    (continuousRepresentation ρ g).adjoint=continuousRepresentation ρ g⁻¹ := by
  ext w
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (unitary_inner_inv ρ hρ g v w).symm

noncomputable def weightedOperator (ρ : Representation ℂ G V) (p : G → ℝ) : V →L[ℂ] V :=
  ∑ g, (p g : ℂ) • continuousRepresentation ρ g

lemma weightedOperator_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, 0≤p g) : ‖weightedOperator ρ p‖ ≤ ∑ g, p g := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp g)]
  exact mul_le_of_le_one_right (hp g) (continuousRepresentation_norm_le ρ hρ g)

lemma weightedOperator_symmetric (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, p g⁻¹=p g) : IsSelfAdjoint (weightedOperator ρ p) := by
  change (weightedOperator ρ p).adjoint=weightedOperator ρ p
  unfold weightedOperator
  rw [map_sum]
  simp only [map_smulₛₗ,Complex.conj_ofReal,continuousRepresentation_adjoint ρ hρ]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  simp [hp]

noncomputable def uniformOperator (ρ : Representation ℂ G V) : V →L[ℂ] V :=
  weightedOperator ρ (fun _ => (Fintype.card G:ℝ)⁻¹)

lemma uniformOperator_symmetric (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) :
    IsSelfAdjoint (uniformOperator ρ) := weightedOperator_symmetric ρ hρ _ (fun _ => rfl)

lemma uniformOperator_left (ρ : Representation ℂ G V) (g : G) :
    continuousRepresentation ρ g * uniformOperator ρ=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma uniformOperator_right (ρ : Representation ℂ G V) (g : G) :
    uniformOperator ρ * continuousRepresentation ρ g=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

lemma uniformOperator_idempotent (ρ : Representation ℂ G V) :
    IsIdempotentElem (uniformOperator ρ) := by
  change uniformOperator ρ * uniformOperator ρ=uniformOperator ρ
  nth_rw 1 [uniformOperator,weightedOperator]
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,uniformOperator_left,Finset.sum_const,Finset.card_univ,
    ←Nat.cast_smul_eq_nsmul ℂ,smul_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma uniformOperator_projection (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) :
    IsStarProjection (uniformOperator ρ) :=
  ⟨uniformOperator_idempotent ρ,uniformOperator_symmetric ρ hρ⟩

lemma weighted_uniform_left (ρ : Representation ℂ G V) (p : G → ℝ) :
    weightedOperator ρ p * uniformOperator ρ=(∑ g,p g : ℝ) • uniformOperator ρ := by
  unfold weightedOperator
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,uniformOperator_left,←Finset.sum_smul,←Complex.ofReal_sum]
  rfl

lemma weighted_uniform_right (ρ : Representation ℂ G V) (p : G → ℝ) :
    uniformOperator ρ * weightedOperator ρ p=(∑ g,p g : ℝ) • uniformOperator ρ := by
  unfold weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,uniformOperator_right,←Finset.sum_smul,←Complex.ofReal_sum]
  rfl

/-- A finite Doeblin minorant gives a dimension-free contraction off invariants;
no irreducible decomposition or unproved spectral-gap hypothesis is used. -/
theorem doeblin_off_invariants (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∑ g,p g=1) (ε : ℝ)
    (hminor : ∀ g, ε/(Fintype.card G:ℝ)≤p g) :
    ‖weightedOperator ρ p * (1-uniformOperator ρ)‖≤1-ε := by
  let q : G → ℝ := fun g => p g-ε/(Fintype.card G:ℝ)
  have hq : ∀ g, 0≤q g := fun g => sub_nonneg.mpr (hminor g)
  have hcard : (Fintype.card G:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ g,q g=1-ε := by
    simp only [q,Finset.sum_sub_distrib,hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have he : weightedOperator ρ p=weightedOperator ρ q+(ε:ℂ) • uniformOperator ρ := by
    simp only [uniformOperator,weightedOperator]
    rw [Finset.smul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    simp only [q,Complex.ofReal_sub,Complex.ofReal_div,smul_smul,←add_smul,
      Complex.ofReal_inv,Complex.ofReal_natCast]
    congr 1
    field_simp
    ring
  have hz : uniformOperator ρ*(1-uniformOperator ρ)=0 := by
    rw [mul_sub,mul_one,(uniformOperator_idempotent ρ).eq,sub_self]
  rw [he,add_mul,smul_mul_assoc,hz,smul_zero,add_zero]
  calc
    _ ≤ ‖weightedOperator ρ q‖*‖1-uniformOperator ρ‖ := norm_mul_le _ _
    _ ≤ (1-ε)*1 := mul_le_mul (by rw [←hsum]; exact weightedOperator_norm_le ρ hρ q hq)
      ((uniformOperator_projection ρ hρ).one_sub.norm_le _) (norm_nonneg _)
      (by rw [←hsum]; exact Finset.sum_nonneg (fun g _ => hq g))
    _ = _ := mul_one _

end CubeShuffle.UnitaryFinite
namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma weightedOperator_conv (ρ : Representation ℂ G V) (p q : G → ℝ) :
    weightedOperator ρ (FiniteConvolution.conv p q)=weightedOperator ρ p*weightedOperator ρ q := by
  unfold weightedOperator FiniteConvolution.conv
  simp only [Complex.ofReal_sum,Finset.sum_smul]
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,←map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
  intro g
  simp [Complex.ofReal_mul,mul_comm]

lemma weightedOperator_power (ρ : Representation ℂ G V) (p : G → ℝ) (n : ℕ) :
    weightedOperator ρ (FiniteConvolution.power p n)=(weightedOperator ρ p)^n := by
  induction n with
  | zero => simp [FiniteConvolution.power,weightedOperator]
  | succ n ih => rw [FiniteConvolution.power,weightedOperator_conv,ih,pow_succ']

lemma off_invariants_pow (ρ : Representation ℂ G V) (p : G → ℝ)
    (hp : ∑ g,p g=1) (n : ℕ) (hn : n≠0) :
    (weightedOperator ρ p-uniformOperator ρ)^n=
      (weightedOperator ρ p)^n*(1-uniformOperator ρ) := by
  have hAP := weighted_uniform_left ρ p
  have hPA := weighted_uniform_right ρ p
  rw [hp,one_smul] at hAP hPA
  have hc : Commute (weightedOperator ρ p) (1-uniformOperator ρ) := by
    show _*_= _*_
    rw [mul_sub,sub_mul,mul_one,one_mul,hAP,hPA]
  have he : weightedOperator ρ p-uniformOperator ρ=
      weightedOperator ρ p*(1-uniformOperator ρ) := by rw [mul_sub,mul_one,hAP]
  rw [he,hc.mul_pow,((uniformOperator_idempotent ρ).one_sub).pow_eq hn]

/-- Explicit gap from the finite-time minorant; its value depends only on the
finite group law, not on the dimension of any represented space. -/
noncomputable def minorantGap {p : G → ℝ} (c : FiniteConvolution.Minorant p) : ℝ :=
  1-c.mass/(2*(2:ℝ)^c.exponent)

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_pos {p : G → ℝ} (c : FiniteConvolution.Minorant p) : 0 < minorantGap c := by
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  unfold minorantGap
  linarith

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_lt_one {p : G → ℝ} (c : FiniteConvolution.Minorant p) : minorantGap c < 1 := by
  unfold minorantGap
  exact sub_lt_self _ (div_pos c.mass_pos (by positivity))

/-- The one-block strict contraction follows from generation and the genuine
holding probability via Doeblin; this is uniform over ALL unitary representations. -/
theorem norm_off_invariants_le_gap (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∑ g,p g=1) (hsym : ∀ g,p g⁻¹=p g)
    (c : FiniteConvolution.Minorant p) :
    ‖weightedOperator ρ p-uniformOperator ρ‖ ≤ minorantGap c := by
  have hself := (weightedOperator_symmetric ρ hρ p hsym).sub (uniformOperator_symmetric ρ hρ)
  have hbound := doeblin_off_invariants ρ hρ (FiniteConvolution.power p (2^c.exponent))
    (FiniteConvolution.sum_power hp _) c.mass c.lower
  rw [weightedOperator_power,←off_invariants_pow ρ p hp _ (by positivity),
    hself.norm_pow_two_pow] at hbound
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  have hbern := one_add_mul_le_pow
    (a := -(c.mass/(2*(2:ℝ)^c.exponent))) (by linarith : (-2:ℝ) ≤ -(c.mass/(2*(2:ℝ)^c.exponent)))
    (2^c.exponent)
  have he : 1+(2^c.exponent:ℕ)*(-(c.mass/(2*(2:ℝ)^c.exponent)))=1-c.mass/2 := by
    push_cast
    field_simp
    ring
  rw [he,show 1+ -(c.mass/(2*(2:ℝ)^c.exponent))=minorantGap c by rfl] at hbern
  by_contra h
  have hlt : minorantGap c < ‖weightedOperator ρ p-uniformOperator ρ‖ := lt_of_not_ge h
  have hpows := pow_lt_pow_left₀ hlt (minorantGap_pos c).le (by positivity : (2^c.exponent:ℕ)≠0)
  linarith [c.mass_pos]

end CubeShuffle.UnitaryFinite

namespace CubeShuffle.FiniteAverage
open scoped BigOperators Classical
variable {I Ω A : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    [Ring A] [Algebra ℂ A]

noncomputable def orderedProduct : MultilinearMap ℂ (fun _ : I => A) A :=
  MultilinearMap.domDomCongr (Fintype.equivFin I).symm
    (MultilinearMap.mkPiAlgebraFin ℂ (Fintype.card I) A)

lemma orderedProduct_eq (f : I → A) (hc : Pairwise fun i j => Commute (f i) (f j)) :
    orderedProduct f=Finset.univ.noncommProd f (fun _ _ _ _ hij => hc hij) := by
  unfold orderedProduct
  rw [MultilinearMap.domDomCongr_apply,MultilinearMap.mkPiAlgebraFin_apply]
  let l := List.ofFn (Fintype.equivFin I).symm
  have hl : l.Nodup := List.nodup_ofFn.mpr (Fintype.equivFin I).symm.injective
  have hu : l.toFinset=Finset.univ := by
    ext i
    simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_univ,iff_true,l]
    exact (Fintype.equivFin I).symm.surjective i
  have he := Finset.noncommProd_toFinset l f (by intro i hi j hj hij; exact hc hij) hl
  rw [hu] at he
  rw [he]
  congr 1
  exact List.map_ofFn.symm

lemma multilinear_average (F : MultilinearMap ℂ (fun _ : I => A) A) (x : I → Ω → A) :
    F (fun i => (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)=
      (Fintype.card (I → Ω):ℂ)⁻¹ • ∑ ω : I → Ω,F (fun i => x i (ω i)) := by
  rw [F.map_smul_univ,F.map_sum]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,inv_pow]

/-- Exact independence factorization for commuting finite random factors. -/
lemma ordered_average (x : I → Ω → A)
    (hc : ∀ ω, Pairwise fun i j => Commute (x i (ω i)) (x j (ω j)))
    (havg : Pairwise fun i j => Commute ((Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)
      ((Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x j ω)) :
    (Finset.univ.noncommProd (fun i => (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)
      (fun _ _ _ _ hij => havg hij))=
    (Fintype.card (I → Ω):ℂ)⁻¹ • ∑ ω : I → Ω,
      Finset.univ.noncommProd (fun i => x i (ω i)) (fun _ _ _ _ hij => hc ω hij) := by
  rw [←orderedProduct_eq _ havg,multilinear_average]
  simp only [orderedProduct_eq _ (hc _)]

end CubeShuffle.FiniteAverage

end OAI
