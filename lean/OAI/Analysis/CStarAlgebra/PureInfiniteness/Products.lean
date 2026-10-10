import OAI.Analysis.CStarAlgebra.PureInfiniteness.Shrinking

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance boundedSlotsOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance boundedSlotsStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma cut_le_self {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 ≤ δ) : cut a δ ≤ a := by
  have he : cfcₙ (fun t : ℝ => t) a = a := cfcₙ_id ℝ a ha.isSelfAdjoint
  conv_rhs => rw [← he]
  change cfcₙ (fun t : ℝ => max (t-δ) 0) a ≤ cfcₙ (fun t : ℝ => t) a
  exact cfcₙ_mono (fun t ht => max_le (by linarith) (quasispectrum_nonneg_of_nonneg a ha t ht))
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    continuousOn_id (by simp [max_eq_right (neg_nonpos.mpr hδ)]) rfl

lemma norm_cut_le {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 ≤ δ) : ‖cut a δ‖ ≤ ‖a‖ :=
  CStarAlgebra.norm_le_norm_of_le_of_nonneg (cut_le_self ha hδ) (cut_nonneg a δ)

lemma cutInverse_nonneg {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ cutInverse a δ := by
  apply cfcₙ_nonneg
  intro t ht
  exact (cutInverseFn_bound hδ (quasispectrum_nonneg_of_nonneg a ha t ht)).1

lemma fixed_of_outer_fixed {F r : A} (h : F*(r*star r)=r*star r) : F*r=r := by
  apply sub_eq_zero.mp
  apply (CStarRing.mul_star_self_eq_zero_iff _).mp
  have hs : r*star r*star F = r*star r := by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star h
  calc
    (F*r-r)*star (F*r-r) = F*(r*star r)*star F - F*(r*star r) - r*star r*star F+r*star r := by
      simp only [star_sub, star_mul]
      noncomm_ring
    _ = 0 := by rw [h, hs]; noncomm_ring

lemma cutInverse_fixed_carrier {a r : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ)
    (hr : r*star r ∈ Her (cut a δ)) : (cutInverse a δ*a)*r=r := by
  have hFsa : IsSelfAdjoint (cutInverse a δ*a) := by
    have hcomm : Commute (cutInverse a δ) a := (Commute.refl a).cfcₙ_real (cutInverseFn δ)
    exact (IsSelfAdjoint.commute_iff (cutInverse_nonneg ha hδ).isSelfAdjoint ha.isSelfAdjoint).mp hcomm
  have ht := Her_right_fixed_cutInverse ha hδ hr
  have hs : (cutInverse a δ*a)*(r*star r)=r*star r := by
    simpa only [star_mul, star_star, hFsa.star_eq] using congrArg star ht
  exact fixed_of_outer_fixed hs

theorem bounded_two_slots (hp : PropertyP A) {d : A} (hd : 0 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Fin 2 → A,
      (∀ i j, star (s i)*d*s j = if i=j then cut d (δ+δ) else 0) ∧
      (∀ i, ‖s i‖ ≤ Real.sqrt (1/δ) * Real.sqrt ‖d‖) := by
  let h := cut d δ
  let k := cut h δ
  have hh : 0 ≤ h := cut_nonneg d δ
  have hk : 0 ≤ k := cut_nonneg h δ
  obtain ⟨S⟩ := (hp h hh).orthogonalSlots hh 2 hδ
  let z : Her k := ⟨CFC.sqrt k, sqrt_mem_Her (self_mem_Her hk) hk⟩
  let r := fun i => S.carrier i z
  let v := CFC.sqrt (cutInverse d δ)
  have hv : 0 ≤ cutInverse d δ := cutInverse_nonneg hd hδ
  have hvr : ∀ i, (cutInverse d δ*d)*r i=r i := fun i =>
    cutInverse_fixed_carrier hd hδ (S.outer i i z z)
  have hvd : star v*d*v=cutInverse d δ*d := by
    have hc : Commute v d := by
      exact ((Commute.refl d).cfcₙ_real (cutInverseFn δ)).cfcₙ_nnreal NNReal.sqrt
    rw [(CFC.sqrt_nonneg (cutInverse d δ)).isSelfAdjoint.star_eq]
    calc
      v*d*v = v*v*d := by rw [mul_assoc, ← hc.eq, ← mul_assoc]
      _ = cutInverse d δ*d := by rw [show v*v=cutInverse d δ from CFC.sqrt_mul_sqrt_self _ hv]
  refine ⟨fun i => v*r i, ?_, ?_⟩
  · intro i j
    calc
      star (v*r i)*d*(v*r j) = star (r i)*(star v*d*v)*r j := by simp only [star_mul]; noncomm_ring
      _ = star (r i)*r j := by rw [hvd, mul_assoc, hvr]
      _ = if i=j then cut d (δ+δ) else 0 := by
        rw [S.inner]
        have he : k=cut d (δ+δ) := cut_cut hd hδ.le hδ.le
        change (if i=j then star (CFC.sqrt k)*CFC.sqrt k else 0) = if i=j then cut d (δ+δ) else 0
        rw [(CFC.sqrt_nonneg k).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hk, he]
  · intro i
    calc
      ‖v*r i‖ ≤ ‖v‖*‖r i‖ := norm_mul_le _ _
      _ ≤ Real.sqrt (1/δ) * Real.sqrt ‖d‖ := by
        apply mul_le_mul
        · rw [CFC.norm_sqrt _ hv]
          exact Real.sqrt_le_sqrt (norm_cutInverse_le hd hδ)
        · rw [S.norm_carrier, CFC.norm_sqrt _ hk]
          exact Real.sqrt_le_sqrt ((norm_cut_le hh hδ.le).trans (norm_cut_le hd hδ.le))
        · exact norm_nonneg _
        · positivity
end MainGap

namespace MainGap
open scoped ENNReal
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)]
local instance productFactorOrder (i : I) : PartialOrder (E i) := CStarAlgebra.spectralOrder _
local instance productFactorStarOrder (i : I) : StarOrderedRing (E i) := CStarAlgebra.spectralOrderedRing _
local instance boundedProductOrder : PartialOrder (lp E ∞) := CStarAlgebra.spectralOrder _
local instance boundedProductStarOrder : StarOrderedRing (lp E ∞) := CStarAlgebra.spectralOrderedRing _

def lpEval (i : I) : lp E ∞ →⋆ₙₐ[ℂ] E i where
  toFun f := f i
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] lemma lpEval_apply (i : I) (f : lp E ∞) : lpEval i f=f i := rfl

def lpBuild (f : ∀ i, E i) (M : ℝ) (h : ∀ i, ‖f i‖ ≤ M) : lp E ∞ :=
  ⟨f, memℓp_infty ⟨M, by rintro t ⟨i,rfl⟩; exact h i⟩⟩

@[simp] lemma lpBuild_apply (f : ∀ i, E i) (M : ℝ) (h : ∀ i, ‖f i‖ ≤ M) (i : I) :
    lpBuild f M h i = f i := rfl

lemma lp_nonneg_iff (d : lp E ∞) : 0 ≤ d ↔ ∀ i, 0 ≤ d i := by
  constructor
  · intro hd i
    exact map_nonneg (lpEval i) hd
  · intro hd
    let v := lpBuild (fun i => CFC.sqrt (d i)) (Real.sqrt ‖d‖) (fun i => by
      rw [CFC.norm_sqrt (d i) (hd i)]
      exact Real.sqrt_le_sqrt (lp.norm_apply_le_norm ENNReal.top_ne_zero d i))
    have he : star v*v=d := by
      ext i
      change star (CFC.sqrt (d i))*CFC.sqrt (d i)=d i
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ (hd i)]
    rw [← he]
    exact star_mul_self_nonneg v

theorem propertyP_lp (hp : ∀ i, PropertyP (E i)) : PropertyP (lp E ∞) := by
  intro d hd
  apply finiteCuntzLE_of_forall_approx
  intro ε hε
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd' : ∀ i, 0 ≤ d i := (lp_nonneg_iff d).mp hd
  choose s hs hn using fun i => bounded_two_slots (hp i) (hd' i) hδ
  have hb (i : I) (j : Fin 2) :
      ‖s i j‖ ≤ Real.sqrt (1/δ)*Real.sqrt ‖d‖ :=
    (hn i j).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (lp.norm_apply_le_norm ENNReal.top_ne_zero d i)) (Real.sqrt_nonneg _))
  let S : Fin 2 → lp E ∞ := fun j => lpBuild (fun i => s i j) _ (fun i => hb i j)
  let R : CStarMatrix (Fin 1) (Fin 2) (lp E ∞) := CStarMatrix.ofMatrix (fun _ j => S j)
  have he : R.conjTranspose * scalarCorner d * R = doubleCorner (cut d (δ+δ)) := by
    apply CStarMatrix.ext
    intro j k
    apply lp.ext
    funext i
    change ((∑ l : Fin 1, (∑ m : Fin 1, star (R m j)*scalarCorner d m l)*R l k) i) =
      (Matrix.diagonal (fun _ : Fin 2 => cut d (δ+δ)) j k) i
    simp only [Fin.sum_univ_one]
    change star (s i j)*d i*s i k=(if j=k then cut d (δ+δ) else 0) i
    rw [hs i j k]
    split_ifs with hjk
    · exact (map_cut (lpEval i) hd (show 0 ≤ δ+δ by positivity)).symm
    · rfl
  refine ⟨R,?_⟩
  rw [he]
  change ‖diagonalHom 2 d - diagonalHom 2 (cut d (δ+δ))‖ < ε
  rw [← map_sub]
  exact ((NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := lp E ∞) 2) _).trans
    (norm_sub_cut_le hd (by positivity))).trans_lt (by dsimp [δ]; linarith)

end MainGap

namespace MainGap
open scoped ENNReal
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)] [DecidableEq I]

lemma lp_single_mem_Her (i : I) {p : lp E ∞} {x : E i} (hx : x ∈ Her (p i)) :
    lp.single ∞ i x ∈ Her p := by
  have hc : IsClosed {x : E i | lp.single ∞ i x ∈ Her p} :=
    (isClosed_Her p).preimage (lp.isometry_single i).continuous
  apply closure_minimal (s := Set.range (fun b : E i => p i*b*star (p i))) _ hc hx
  rintro x ⟨b,rfl⟩
  change lp.single ∞ i (p i*b*star (p i)) ∈ Her p
  have he : lp.single ∞ i (p i*b*star (p i)) = p*lp.single ∞ i b*star p := by
    apply lp.ext
    funext j
    by_cases hj : j=i
    · subst j
      change lp.single ∞ i (p i*b*star (p i)) i = p i*lp.single ∞ i b i*star (p i)
      simp only [lp.single_apply_self]
    · change lp.single ∞ i (p i*b*star (p i)) j = p j*lp.single ∞ i b j*star (p j)
      rw [lp.single_apply_ne _ _ _ hj, lp.single_apply_ne _ _ _ hj, mul_zero, zero_mul]
  rw [he]
  exact sandwich_mem_Her p _

lemma HerCompression.lp_eval {p q c : lp E ∞} {κ : ℝ}
    (h : HerCompression p q c κ) (i : I) : HerCompression (p i) (q i) (c i) κ := by
  intro x hx k hk
  have hi := h _ (lp_single_mem_Her i hx) _ (lp_single_mem_Her i hk)
  have he : lp.single ∞ i x*c*lp.single ∞ i k = lp.single ∞ i (x*c i*k) := by
    apply lp.ext
    funext j
    by_cases hj : j=i
    · subst j
      change lp.single ∞ i x i*c i*lp.single ∞ i k i=lp.single ∞ i (x*c i*k) i
      simp only [lp.single_apply_self]
    · change lp.single ∞ i x j*c j*lp.single ∞ i k j=lp.single ∞ i (x*c i*k) j
      rw [lp.single_apply_ne _ _ _ hj, lp.single_apply_ne _ _ _ hj,
        lp.single_apply_ne _ _ _ hj, zero_mul, mul_zero]
  rw [he, lp.norm_single (by simp : (0 : ℝ≥0∞)<∞),
    lp.norm_single (by simp : (0 : ℝ≥0∞)<∞),
    lp.norm_single (by simp : (0 : ℝ≥0∞)<∞)] at hi
  exact hi
end MainGap

namespace MainGap
open scoped ENNReal
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
local instance sequenceFactorOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance sequenceFactorStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance boundedSequenceOrder : PartialOrder (lp (fun _ : ℕ => A) ∞) := CStarAlgebra.spectralOrder _
local instance boundedSequenceStarOrder : StarOrderedRing (lp (fun _ : ℕ => A) ∞) := CStarAlgebra.spectralOrderedRing _

lemma NormSignal.lp_eval {a p : lp (fun _ : ℕ => A) ∞} (h : NormSignal a p) (i : ℕ) :
    NormSignal (a i) (p i) := by
  intro R hR
  let S : HilbertRep.{u,u} (Unitization ℂ (lp (fun _ : ℕ => A) ∞)) :=
    { R with hom := R.hom.comp (Unitization.starMap (lpEval i)) }
  have he (x : lp (fun _ : ℕ => A) ∞) :
      S.hom (x : Unitization ℂ (lp (fun _ : ℕ => A) ∞)) =
        R.hom (x i : Unitization ℂ A) := by
    simp [S]
  have hr : (1/2:ℝ)<‖S.hom (a : Unitization ℂ (lp (fun _ : ℕ => A) ∞))‖ := by
    rwa [he]
  have ht := h S hr
  rwa [he] at ht

theorem uniform_shrinking (hp : PropertyP A) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ a y c : A, 0 ≤ a → ‖a‖ ≤ 1 → 0 ≤ y → ‖y‖ ≤ 1 → ‖c‖ ≤ 1 →
        ∃ p q : A, 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
          0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her y ∧
          HerCompression p q c θ ∧ NormSignal a p ∧ NormSignal y q := by
  classical
  by_contra hn
  push Not at hn
  let θ : ℕ → ℝ := fun n => 1-1/((n:ℝ)+2)
  have hθ0 (n : ℕ) : 0 < θ n := by
    dsimp [θ]
    have h : (1:ℝ)/((n:ℝ)+2)<1 := (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hθ1 (n : ℕ) : θ n < 1 := by
    dsimp [θ]
    have : 0 < (1:ℝ)/((n:ℝ)+2) := by positivity
    linarith
  choose a y c ha han hy hyn hcn hfail using fun n => hn (θ n) (hθ0 n) (hθ1 n)
  let a' : lp (fun _ : ℕ => A) ∞ := lpBuild a 1 han
  let y' : lp (fun _ : ℕ => A) ∞ := lpBuild y 1 hyn
  let c' : lp (fun _ : ℕ => A) ∞ := lpBuild c 1 hcn
  have ha' : 0 ≤ a' := (lp_nonneg_iff a').mpr ha
  have hy' : 0 ≤ y' := (lp_nonneg_iff y').mpr hy
  have hyn' : ‖y'‖ ≤ 1 := lp.norm_le_of_forall_le (by norm_num) hyn
  have hcn' : ‖c'‖ ≤ 1 := lp.norm_le_of_forall_le (by norm_num) hcn
  obtain ⟨p,q,κ,hp0,hpn,hpH,hq0,hqn,hqH,hκ0,hκ1,hcomp,hps,hqs⟩ :=
    shrinking_nonunital (propertyP_lp (fun _ : ℕ => hp)) ha' hy' hyn' hcn'
  obtain ⟨n,hnκ⟩ := exists_nat_gt (1/(1-κ))
  have hκθ : κ ≤ θ n := by
    have hn2 : 1/(1-κ) < (n:ℝ)+2 := by linarith
    have hmul : (1:ℝ) < ((n:ℝ)+2)*(1-κ) := (div_lt_iff₀ (by linarith)).mp hn2
    have hdiv : 1/((n:ℝ)+2) < 1-κ := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
    dsimp [θ]; linarith
  apply hfail n (p n) (q n)
  · exact (lp_nonneg_iff p).mp hp0 n
  · exact (lp.norm_apply_le_norm ENNReal.top_ne_zero p n).trans hpn
  · exact Her_map (lpEval n) hpH
  · exact (lp_nonneg_iff q).mp hq0 n
  · exact (lp.norm_apply_le_norm ENNReal.top_ne_zero q n).trans hqn
  · exact Her_map (lpEval n) hqH
  · intro x hx k hk
    exact ((hcomp.lp_eval n) x hx k hk).trans (by gcongr)
  · exact hps.lp_eval n
  · exact hqs.lp_eval n
end MainGap

end

end OAI
