import OAI.Analysis.Littlewood.QuadraticTail

namespace OAI

universe uI uE uJ uK

namespace AsymptoticallyMinimalLittlewood
namespace Spreading
noncomputable section
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap

/-- The uniform stationary-phase bound in the squared, scale-invariant form
needed for every retained spread Fourier coefficient. -/
lemma quadratic_norm_scaled {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1)
    {β : ℝ} (hβ : β≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 0<T → ∀ u : ℝ,
      T*|β| *‖∫ x : ℝ, g x*phase (T*β) u x‖^2 ≤ (1+C/T)^2 := by
  let C := Real.pi / |β| * (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ,ℂ)) ξ‖)
  have hC : 0≤C := mul_nonneg (div_nonneg Real.pi_pos.le (abs_nonneg _))
    (integral_nonneg (fun ξ ↦ mul_nonneg (sq_nonneg _) (norm_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro T hT u
  obtain ⟨E,hE,he⟩ := uniform_quadratic_integration g hg hgs hβ hT u
  change ‖E‖≤C/T at hE
  change (∫ x : ℝ, g x*phase (T*β) u x) = _ at he
  have hphase : ‖realPhase (2*Real.pi*(Real.sign β/8-u^2/(2*T*β)))‖ = 1 := by
    exact norm_realPhase _
  have hsqrt : 0<Real.sqrt (T*|β|) := Real.sqrt_pos.mpr (mul_pos hT (abs_pos.mpr hβ))
  have hn : ‖g (u/(T*β))+E‖≤1+C/T :=
    (norm_add_le _ _).trans (add_le_add (hg1 _) hE)
  have hnorm : ‖∫ x : ℝ, g x*phase (T*β) u x‖ =
      ‖g (u/(T*β))+E‖/Real.sqrt (T*|β|) := by
    rw [he,norm_mul,norm_div,hphase,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsqrt]
    ring
  rw [hnorm,div_pow,Real.sq_sqrt (mul_pos hT (abs_pos.mpr hβ)).le]
  have hc : 0≤1+C/T := by positivity
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    _ = ‖g (u/(T*β))+E‖^2 := by field_simp
    _ ≤ _ := hn2

variable {I : Type uI} [Fintype I] [DecidableEq I]

def multiBox (B : ℝ) (β : I → ℝ) : Finset (I → ℤ) :=
  Fintype.piFinset (fun i ↦ box B (β i))

def determinant (β : I → ℝ) : ℝ := ∏ i, |β i|

omit [DecidableEq I] in
lemma determinant_pos {β : I → ℝ} (hβ : ∀ i, β i≠0) : 0<determinant β :=
  Finset.prod_pos (fun i _ ↦ abs_pos.mpr (hβ i))

lemma multiBox_card_bound {B : ℝ} (hB : 0<B) (β : I → ℝ) :
    ((multiBox B β).card : ℝ) ≤ B^(Fintype.card I) * ∏ i, (|β i|+1/B) := by
  rw [multiBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    _ ≤ ∏ i, (B*|β i|+1) := Finset.prod_le_prod₀ (fun i _ ↦ Nat.cast_nonneg _)
      (fun i _ ↦ box_card_le hB.le _)
    _ = ∏ i, B*(|β i|+1/B) := by
      apply Finset.prod_congr rfl
      intro i _
      field_simp
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma multiBox_eventual_card {β : I → ℝ} (hβ : ∀ i, β i≠0)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ B : ℝ in atTop, ((multiBox B β).card : ℝ) ≤
      (1+ε)*B^(Fintype.card I)*determinant β := by
  have hd := determinant_pos hβ
  have hi : Tendsto (fun B : ℝ ↦ 1/B) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hp : Tendsto (fun B : ℝ ↦ ∏ i, (|β i|+1/B)) atTop (𝓝 (determinant β)) := by
    simpa only [add_zero,determinant] using tendsto_finsetProd Finset.univ
      (fun i _ ↦ tendsto_const_nhds.add hi)
  have hg : ∀ᶠ B : ℝ in atTop, (∏ i, (|β i|+1/B)) ≤ (1+ε)*determinant β :=
    (hp.eventually (eventually_lt_nhds (by nlinarith : determinant β < (1+ε)*determinant β))).mono (fun _ h ↦ h.le)
  filter_upwards [hg,eventually_gt_atTop (0:ℝ)] with B hb hB
  calc
    _ ≤ B^(Fintype.card I)*(∏ i, (|β i|+1/B)) := multiBox_card_bound hB β
    _ ≤ B^(Fintype.card I)*((1+ε)*determinant β) := mul_le_mul_of_nonneg_left hb (pow_nonneg hB.le _)
    _ = _ := by ring

omit [DecidableEq I] in

lemma tensor_coefficient_eventual {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {β : I → ℝ}
    (hβ : ∀ i, β i≠0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ B : ℝ in atTop, ∀ u : I → ℤ,
      B^(Fintype.card I)*determinant β *
        ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2 ≤ 1+ε := by
  choose C hC hc using (fun i ↦ quadratic_norm_scaled hg hgs hg1 (hβ i))
  have hi : Tendsto (fun B : ℝ ↦ 1/B) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hp : Tendsto (fun B : ℝ ↦ ∏ i, (1+C i/B)^2) atTop (𝓝 1) := by
    have h (i : I) : Tendsto (fun B : ℝ ↦ (1+C i/B)^2) atTop (𝓝 1) := by
      have hci : Tendsto (fun B : ℝ ↦ C i/B) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.div_atTop tendsto_id)
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hci).pow 2
    simpa using tendsto_finsetProd Finset.univ (fun i _ ↦ h i)
  have hp' : ∀ᶠ B : ℝ in atTop, (∏ i, (1+C i/B)^2) ≤ 1+ε :=
    (hp.eventually (eventually_lt_nhds (by linarith : (1:ℝ) < 1+ε))).mono (fun _ h ↦ h.le)
  filter_upwards [hp',eventually_gt_atTop (0:ℝ)] with B hb hB
  intro u
  calc
    _ = ∏ i, (B*|β i| *‖∫ x : ℝ, g x*phase (B*β i) (u i) x‖^2) := by
      rw [norm_prod,← Finset.prod_pow]
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,determinant]
    _ ≤ ∏ i, (1+C i/B)^2 := Finset.prod_le_prod₀
      (fun i _ ↦ mul_nonneg (mul_nonneg hB.le (abs_nonneg _)) (sq_nonneg _))
      (fun i _ ↦ hc i B hB (u i))
    _ ≤ _ := hb

lemma row_mass_le {g : ℝ → ℂ} (hgs : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (T β : ℝ) :
    (∑ w ∈ box T β, ‖∫ x : ℝ, g x*phase (T*β) w x‖^2) ≤
      ∫ x : ℝ, ‖g x‖^2 := by
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs hα hs _⟩
  have hp := circle_parseval f
  have hb := hp.summable.sum_le_tsum (box T β) (fun w _ ↦ sq_nonneg _)
  rw [hp.tsum_eq] at hb
  change (∑ w ∈ box T β, ‖fourierCoeff (circleChirp g (T*β)) w‖^2) ≤
    ∫ z : UnitAddCircle, ‖circleChirp g (T*β) z‖^2 ∂AddCircle.haarAddCircle at hb
  simpa only [circleChirp_coefficient hα hs,circleChirp_mass hα hs] using hb

lemma row_mass_tendsto {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : ℝ} (hβ : β≠0) :
    Tendsto (fun T : ℝ ↦ ∑ w ∈ box T β,
      ‖∫ x : ℝ, g x*phase (T*β) w x‖^2) atTop (𝓝 (∫ x : ℝ, ‖g x‖^2)) := by
  obtain ⟨C,hC,h⟩ := row_mass_error hg hgs hg1 hα0 hα hs hβ
  have hi : Tendsto (fun T : ℝ ↦ C/T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hi) tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT using h T hT
  · exact Eventually.of_forall (fun T ↦ row_mass_le hgs.continuous hα hs T β)

lemma tensor_mass_tendsto {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : I → ℝ} (hβ : ∀ i, β i≠0) :
    Tendsto (fun B : ℝ ↦ ∑ u ∈ multiBox B β,
      ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2)
      atTop (𝓝 ((∫ x : ℝ, ‖g x‖^2)^(Fintype.card I))) := by
  have he (B : ℝ) : (∑ u ∈ multiBox B β,
      ‖∏ i, (∫ x : ℝ, g x*phase (B*β i) (u i) x)‖^2) =
      ∏ i, (∑ w ∈ box B (β i), ‖∫ x : ℝ, g x*phase (B*β i) w x‖^2) := by
    simp only [norm_prod,← Finset.prod_pow,multiBox]
    exact (Finset.prod_univ_sum (fun i : I ↦ box B (β i))
      (fun (i : I) (w : ℤ) ↦ ‖∫ x : ℝ, g x*phase (B*β i) w x‖^2)).symm
  simp_rw [he]
  simpa using tendsto_finsetProd Finset.univ
    (fun i _ ↦ row_mass_tendsto hg hgs hg1 hα0 hα hs (hβ i))

omit [DecidableEq I] in
lemma tensor_uniform_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : I → ℝ} (hβ : ∀ i, β i≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ z : I → UnitAddCircle,
      ‖(∏ i, rowTrunc g B (β i) (z i))-
        (∏ i, circleChirp g (B*β i) (z i))‖ ≤ C/B := by
  apply finite_product_error (I := I) (Z := I → UnitAddCircle) Finset.univ
    (fun (i : I) (B : ℝ) (z : I → UnitAddCircle) ↦ rowTrunc g B (β i) (z i))
    (fun (i : I) (B : ℝ) (z : I → UnitAddCircle) ↦ circleChirp g (B*β i) (z i))
  · intro i _ B z
    exact circleChirp_norm hg1 _ _
  · intro i _
    obtain ⟨C,hC,h⟩ := rowTrunc_error hg hgs hα0 hα hs (hβ i)
    exact ⟨C,hC,fun B hB z ↦ h B hB (z i)⟩

end
end Spreading
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex

lemma support_pair_sum {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ)
    (S : Finset (Fin n → ℤ)) (hp : ∀ s ∈ S, positive n s)
    (hc : ∀ s, s ∈ c.support ↔ s ∈ S ∨ -s ∈ S)
    {E : Type uE} [AddCommMonoid E] (f : (Fin n → ℤ) → E) :
    ∑ s ∈ c.support, f s = ∑ s ∈ S, (f s+f (-s)) := by
  classical
  have hd : Disjoint S (S.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro s hs hn
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
    exact positive_not_neg (hp t ht) (hp _ hs)
  have he : c.support = S ∪ S.image Neg.neg := by
    ext s
    simpa only [Finset.mem_union, Finset.mem_image, neg_eq_iff_eq_neg,
      exists_eq_right] using hc s
  rw [he, Finset.sum_union hd, Finset.sum_image (by
    intro x _ y _ h; exact neg_injective h), Finset.sum_add_distrib]

lemma binary_positive_data {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ n : ℕ, ∃ S : Finset (Fin n → ℤ), S.Nonempty ∧
      (∀ s ∈ S, positive n s) ∧ ∃ c : (Fin n → ℤ) → ℂ,
      (∀ s ∈ S, c s≠0) ∧
      (∀ x : Fin n → UnitAddCircle,
        (binary n x : ℂ) = (∑ s ∈ S, c s*mFourier s x) +
          conj (∑ s ∈ S, c s*mFourier s x)) ∧
      1-δ ≤ 2*∑ s ∈ S, ‖c s‖^2 ∧ 2*∑ s ∈ S, ‖c s‖^2 ≤ 1 := by
  classical
  obtain ⟨n,hn,he⟩ := exists_binary_energy hδ
  obtain ⟨c,hp,hc⟩ := exists_binary_coefficients n
  obtain ⟨S,hS,hSp⟩ := coefficient_support_pairs c hp hc
  have hm : 2*∑ s ∈ S, ‖c s‖^2 = energy n := by
    rw [← binary_coefficients_energy c hc, support_pair_sum c S hS hSp]
    simp only [binary_coefficients_conj c hc, norm_conj]
    rw [Finset.sum_add_distrib]
    ring
  have hSn : S.Nonempty := by
    by_contra hz
    have hz' : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hz
    rw [hz'] at hm
    simp only [Finset.sum_empty,mul_zero] at hm
    linarith
  refine ⟨n,S,hSn,hS,c,?_,?_,by linarith,by rw [hm]; exact (energy_bounds n).2⟩
  · intro s hs
    exact Finsupp.mem_support_iff.mp ((hSp s).mpr (Or.inl hs))
  · intro x
    rw [hc, support_pair_sum c S hS hSp, Finset.sum_add_distrib]
    congr 1
    simp only [map_sum,map_mul,binary_coefficients_conj c hc,mFourier_neg]

def rowForm {n : ℕ} (s : Fin n → ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ k, (s k : ℝ) • LinearMap.proj k

lemma rowForm_apply {n : ℕ} (s : Fin n → ℤ) (x : Fin n → ℝ) :
    rowForm s x = ∑ k, (s k : ℝ)*x k := by simp [rowForm]

lemma rowForm_injective {n : ℕ} : Function.Injective (@rowForm n) := by
  classical
  intro s t h
  ext k
  have hh := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.single k 1)) h
  simp [rowForm_apply, Pi.single_apply, mul_ite] at hh
  exact_mod_cast hh

lemma positive_rowForm_ne_zero {n : ℕ} {s : Fin n → ℤ} (hs : positive n s) :
    rowForm s ≠ 0 := by
  intro hz
  apply primitive_ne_zero (positive_primitive hs)
  apply rowForm_injective
  simpa [rowForm] using hz

lemma positive_rowForm_nonparallel {n : ℕ} {s t : Fin n → ℤ}
    (hs : positive n s) (ht : positive n t) (hne : s ≠ t) (c : ℝ) :
    rowForm s ≠ c • rowForm t := by
  classical
  intro he
  apply hne
  apply (positive_parallel_eq hs ht (c := c) ?_).1
  intro k
  have hh := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.single k 1)) he
  simpa [rowForm_apply, Pi.single_apply, mul_ite] using hh

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma mFourier_norm_apply {J : Type uJ} [Fintype J] (s : J → ℤ)
    (x : J → UnitAddCircle) : ‖mFourier s x‖=1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

lemma mFourier_add_point {J : Type uJ} [Fintype J] (s : J → ℤ)
    (x y : J → UnitAddCircle) : mFourier s (x+y)=mFourier s x*mFourier s y := by
  simp only [mFourier, ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,
    zsmul_add,AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]

lemma mFourier_real {J : Type uJ} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    mFourier s (fun j ↦ (x j : UnitAddCircle)) =
      Complex.exp (Complex.I*(2*Real.pi*(∑ j, (s j : ℝ)*x j) : ℝ)) := by
  simp only [mFourier,ContinuousMap.coe_mk,fourier_coe_apply,Complex.ofReal_one,div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_intCast,Complex.ofReal_ofNat,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma phase_tensor_character {n : ℕ} {J : Type uJ} [Fintype J]
    (s : Fin n → ℤ) (b : J → Fin n → ℝ) (B : ℝ) (z : J → ℝ) :
    (∏ j, phase (B*rowForm s (b j)) 0 (z j)) =
      mFourier s (fun k ↦ ((B/2*∑ j, b j k*z j^2 : ℝ) : UnitAddCircle)) := by
  rw [mFourier_real]
  simp only [phase,sub_zero,zero_mul,← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_div,
    Complex.ofReal_ofNat,Complex.ofReal_pow,rowForm_apply]
  push_cast
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma spread_half_bound {n : ℕ} {J : Type uJ} [Fintype J]
    (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ y : Fin n → UnitAddCircle,
      (binary n y : ℂ) = (∑ s ∈ S, c s*mFourier s y)+
        conj (∑ s ∈ S, c s*mFourier s y))
    (g : ℝ → ℝ) (hg : ∀ x, 0≤g x ∧ g x≤1)
    (b : J → Fin n → ℝ) (B : ℝ) (y : Fin n → UnitAddCircle)
    (z : J → UnitAddCircle) :
    ‖(∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j)) +
      conj (∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j))‖ ≤ 1 := by
  let x : J → ℝ := fun j ↦ AddCircle.equivIoc 1 (-1/2) (z j)
  let u : Fin n → UnitAddCircle := fun k ↦ ((B/2*∑ j, b j k*x j^2 : ℝ) : UnitAddCircle)
  let A : ℝ := ∏ j, g (x j)
  have hA0 : 0≤A := Finset.prod_nonneg (fun j _ ↦ (hg _).1)
  have hA1 : A≤1 := Finset.prod_le_one₀ (fun j _ ↦ (hg _).1) (fun j _ ↦ (hg _).2)
  have he : (∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j)) = (A : ℂ)*∑ s∈S, c s*mFourier s (y+u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    have hp : (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)) =
        (A : ℂ)*mFourier s u := by
      change (∏ j, (g (x j) : ℂ)*phase (B*rowForm s (b j)) 0 (x j)) = _
      rw [Finset.prod_mul_distrib,phase_tensor_character]
      simp only [A,Complex.ofReal_prod,u]
    rw [hp,mFourier_add_point]
    ring
  rw [he,map_mul,conj_ofReal,← mul_add,← hc]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA0,
    Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (binary_abs_le n _) hA0).trans (by simpa using hA1)

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma tensor_trunc_expand {J : Type uJ} [Fintype J] [DecidableEq J]
    (g : ℝ → ℂ) (B : ℝ) (β : J → ℝ) (z : J → UnitAddCircle) :
    (∏ j, rowTrunc g B (β j) (z j)) =
      ∑ u∈multiBox B β, (∏ j, ∫ x : ℝ, g x*phase (B*β j) (u j) x)*mFourier u z := by
  classical
  simp only [rowTrunc,multiBox,mFourier,ContinuousMap.coe_mk,← Finset.prod_mul_distrib]
  exact Finset.prod_univ_sum _ _

lemma cutoff_power {D : ℕ} {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∃ α : ℝ, 0<α ∧ α<1/2 ∧ tsupport g ⊆ Set.Icc (-α) α) ∧
      (∀ x, 0≤g x ∧ g x≤1) ∧
      1-δ < (∫ x : ℝ, g x^2)^D := by
  have hD : (0:ℝ)<D+1 := by positivity
  let ε : ℝ := δ/(D+1)
  have hε : 0<ε := div_pos hδ hD
  have hε1 : ε<1 := by dsimp [ε]; rw [div_lt_one hD]; have : (0:ℝ)≤D := Nat.cast_nonneg _; linarith
  obtain ⟨g,hgs,hgc,hga,hg,hm⟩ := Cutoff.unit_cutoff hε
  refine ⟨g,hgs,hgc,hga,hg,?_⟩
  have hb := one_add_mul_le_pow (a := -ε) (by linarith : (-2:ℝ)≤-ε) D
  have hp : (1-ε)^D ≤ (∫ x : ℝ, g x^2)^D := pow_le_pow_left₀ (by linarith) hm.le _
  have hi : (D : ℝ)*ε<δ := by dsimp [ε]; rw [← mul_div_assoc, div_lt_iff₀ hD]; nlinarith
  have hh : 1-δ < 1+(D:ℝ)*(-ε) := by linarith
  exact hh.trans_le (hb.trans (by simpa only [sub_eq_add_neg] using hp))

lemma spread_trunc_eventual_bound {n : ℕ} {J : Type uJ} [Fintype J] [DecidableEq J]
    (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ y : Fin n → UnitAddCircle,
      (binary n y : ℂ) = (∑ s∈S, c s*mFourier s y)+conj (∑ s∈S, c s*mFourier s y))
    {g : ℝ → ℝ} (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hg : ∀ x, 0≤g x ∧ g x≤1) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hga : tsupport g ⊆ Set.Icc (-α) α)
    (b : J → Fin n → ℝ) (hb : ∀ s∈S, ∀ j, rowForm s (b j)≠0)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ B : ℝ in atTop, ∀ y : Fin n → UnitAddCircle, ∀ z : J → UnitAddCircle,
      ‖(∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))+
        conj (∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))‖ ≤ 1+δ := by
  classical
  have hsupp : tsupport (fun x ↦ (g x : ℂ)) = tsupport g := by
    unfold tsupport
    apply congrArg closure
    ext x
    change ((g x : ℂ)≠0) ↔ g x≠0
    exact Complex.ofReal_ne_zero
  have hgc' : HasCompactSupport (fun x ↦ (g x : ℂ)) := by simpa only [HasCompactSupport,hsupp] using hgc
  have hgs' : ContDiff ℝ ∞ (fun x ↦ (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hgs
  have hg' : ∀ x, ‖(g x : ℂ)‖≤1 := by intro x; simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg x).1] using (hg x).2
  have hga' : tsupport (fun x ↦ (g x : ℂ)) ⊆ Set.Icc (-α) α := by
    simpa only [hsupp] using hga
  have hh (s : S) : ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ z : J → UnitAddCircle,
      ‖(∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s.val (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s.val (b j)) (z j))‖≤C/B :=
    tensor_uniform_error hgc' hgs' hg' hα0 hα hga' (hb s.val s.property)
  choose C hC hE using hh
  let A : ℝ := ∑ s : S, ‖c s.val‖*C s
  have hlim : Tendsto (fun B : ℝ ↦ 2*A/B) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ),eventually_ge_atTop (1:ℝ)] with B hBδ hB
  intro y z
  let T : ℂ := ∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j)
  let G : ℂ := ∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)
  have hTG : ‖T-G‖≤A/B := by
    dsimp [T,G]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ s∈S, ‖c s*mFourier s y*((∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)))‖ := by
          simp only [mul_sub]; exact norm_sum_le _ _
      _ = ∑ s : S, ‖c s.val‖*‖(∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s.val (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s.val (b j)) (z j))‖ := by
          simp only [norm_mul,mFourier_norm_apply,mul_one]
          exact (Finset.sum_attach _ _).symm
      _ ≤ ∑ s : S, ‖c s.val‖*(C s/B) := Finset.sum_le_sum (fun s _ ↦ mul_le_mul_of_nonneg_left (hE s B hB z) (norm_nonneg _))
      _ = A/B := by simp only [A,mul_div_assoc,Finset.sum_div]
  have hm := spread_half_bound S c hc g hg b B y z
  change ‖G+conj G‖≤1 at hm
  change ‖T+conj T‖≤1+δ
  have hd : ‖(T+conj T)-(G+conj G)‖≤2*(A/B) := by
    calc
      _ = ‖(T-G)+conj (T-G)‖ := by congr 1; simp only [map_sub]; ring
      _ ≤ ‖T-G‖+‖conj (T-G)‖ := norm_add_le _ _
      _ ≤ 2*(A/B) := by rw [norm_conj]; linarith
  have ht := norm_add_le ((T+conj T)-(G+conj G)) (G+conj G)
  rw [sub_add_cancel] at ht
  have he : 2*(A/B)=2*A/B := by ring
  rw [he] at hd
  linarith

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

structure RawData (I J : Type) [Fintype I] [Fintype J] (δ : ℝ) where
  frequency : I → J → ℤ
  coefficient : I → ℂ
  velocity : J → ℝ
  nonzero : ∀ i, frequency i ≠ 0
  nonparallel : ∀ i i', i≠i' → ∀ t : ℝ,
    ¬∀ j, (frequency i j : ℝ)=t*(frequency i' j : ℝ)
  bounded : ∀ y : J → UnitAddCircle,
    ‖(∑ i, coefficient i*mFourier (frequency i) y)+
      conj (∑ i, coefficient i*mFourier (frequency i) y)‖≤1
  energy : (1-3*δ)^2 ≤ 2*∑ i, ‖coefficient i‖^2
  curvature : ∀ i, (∑ j, (frequency i j : ℝ)*velocity j)≠0
  width : 2*∑ i, |∑ j, (frequency i j : ℝ)*velocity j| < 1
  size : ∀ i, ‖coefficient i‖^2 ≤ ((1+δ)^3/(1-δ))*
    |∑ j, (frequency i j : ℝ)*velocity j|

structure FinitePacket (δ : ℝ) where
  I : Type
  J : Type
  fintypeI : Fintype I
  fintypeJ : Fintype J
  nonemptyI : Nonempty I
  data : @RawData I J fintypeI fintypeJ δ

attribute [instance] FinitePacket.fintypeI FinitePacket.fintypeJ FinitePacket.nonemptyI

lemma mFourier_sum_type {J : Type uJ} {K : Type uK} [Fintype J] [Fintype K]
    (s : J → ℤ) (u : K → ℤ) (x : J ⊕ K → UnitAddCircle) :
    mFourier (Sum.elim s u) x = mFourier s (x ∘ Sum.inl)*mFourier u (x ∘ Sum.inr) := by
  simp only [mFourier,ContinuousMap.coe_mk,Fintype.prod_sum_type,Sum.elim_inl,
    Sum.elim_inr,Function.comp_apply]

lemma spread_numeric_coefficient {δ τ P Δ ρ U V : ℝ}
    (hδ : 0<δ) (hδ1 : δ<1) (hτ : 0<τ) (hP : 0<P) (hρ : 0<ρ)
    (_hU : 0≤U) (hV : 0≤V)
    (hdet : (1-δ)*τ*U/ρ ≤ Δ) (hdisc : P*Δ*V≤(1+δ)^2) :
    U*V/(1+δ)^2 ≤ ((1+δ)^3/(1-δ))*(ρ/(τ*P*(1+δ)^3)) := by
  have hd0 : 0<1-δ := sub_pos.mpr hδ1
  have hd1 : 0<1+δ := by linarith
  have hd2 := mul_le_mul_of_nonneg_right hdet (mul_nonneg hP.le hV)
  have hd3 := mul_le_mul_of_nonneg_left hdisc hρ.le
  have he : ((1-δ)*τ*U/ρ)*(P*V)*ρ=(1-δ)*τ*P*(U*V) := by field_simp
  have hd4 := mul_le_mul_of_nonneg_right hd2 hρ.le
  rw [he] at hd4
  have hraw : (1-δ)*τ*P*(U*V)≤ρ*(1+δ)^2 := by nlinarith only [hd3,hd4]
  have hr : ((1+δ)^3/(1-δ))*(ρ/(τ*P*(1+δ)^3))=ρ/((1-δ)*τ*P) := by
    field_simp
  rw [hr]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd1) (by positivity)).mpr
  nlinarith only [hraw]

lemma spread_numeric_width {δ τ P Δ ρ U L : ℝ}
    (hδ : 0<δ) (hτ : 0<τ) (hP : 0<P) (hρ : 0<ρ)
    (hdet : Δ ≤ (1+δ)*τ*U/ρ) (hcard : L≤(1+δ)*P*Δ) :
    L*(ρ/(τ*P*(1+δ)^3))≤U/(1+δ) := by
  have hd1 : 0<1+δ := by linarith
  have h1 := mul_le_mul_of_nonneg_left hdet (mul_nonneg hd1.le hP.le)
  have h2 := mul_le_mul_of_nonneg_right (hcard.trans h1) hρ.le
  have he : (1+δ)*P*((1+δ)*τ*U/ρ)*ρ=τ*P*(1+δ)^2*U := by field_simp
  rw [he] at h2
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) hd1).mpr
  have hh := mul_le_mul_of_nonneg_right h2 hd1.le
  nlinarith only [hh]

lemma spread_numeric_energy {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1/20) :
    (1-3*δ)^2 ≤ ((1-δ)*(1-2*δ))/(1+δ)^2 := by
  have h1 : 0≤1-3*δ := by linarith
  have h2 : 0≤1-2*δ := by linarith
  have hd : 0<1+δ := by linarith
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  have hh : (1-3*δ)*(1+δ)≤1-2*δ := by nlinarith [sq_nonneg δ]
  have hsq : ((1-3*δ)*(1+δ))^2≤(1-2*δ)^2 := sq_le_sq₀ (mul_nonneg h1 hd.le) h2 |>.mpr hh
  nlinarith [mul_nonneg hδ.le h2]

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

/-- The full Fourier-spreading construction, before adjoining a harmless zero
coefficient to ensure that the packing catalogue has at least two rows. -/
theorem exists_auxiliary_packet {δ : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20) :
    Nonempty (FinitePacket δ) := by
  classical
  have hδ1 : δ<1 := by linarith
  have hd : 0<1+δ := by linarith
  obtain ⟨n,S,hSn,hS,c,hc,hpoly,hElo,hEhi⟩ := binary_positive_data hδ hδ1
  let I := ↥S
  have : Nonempty I := ⟨⟨hSn.choose,hSn.choose_spec⟩⟩
  let f : I → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun i ↦ rowForm i.val
  have hf (i : I) : f i≠0 := positive_rowForm_ne_zero (hS i.val i.property)
  have hfp (i j : I) (hij : i≠j) (t : ℝ) : f i≠t • f j :=
    positive_rowForm_nonparallel (hS i.val i.property) (hS j.val j.property)
      (fun h ↦ hij (Subtype.ext h)) t
  obtain ⟨γ,hγ⟩ := Curvature.exists_generic f hf
  let ρ : I → ℝ := fun i ↦ |f i γ|
  have hρ (i : I) : 0<ρ i := abs_pos.mpr (hγ i)
  have hc0 (i : I) : 0<‖c i.val‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (hc i.val i.property))
  obtain ⟨τ,hτ,b,hb,hdet⟩ := Curvature.determinant_tuning f hf hfp
    (fun i ↦ ‖c i.val‖^2/ρ i) (fun i ↦ div_pos (hc0 i) (hρ i)) hδ hδ1
  let β : I → I → ℝ := fun i j ↦ f i (b j)
  have hβ (i j : I) : β i j≠0 := hb i j
  obtain ⟨g,hgs,hgc,⟨α,hα0,hα,hga⟩,hg,hgm⟩ := cutoff_power (D := Fintype.card I) hδ hδ1
  let g' : ℝ → ℂ := fun x ↦ (g x : ℂ)
  have hgs' : ContDiff ℝ ∞ g' := Complex.ofRealCLM.contDiff.comp hgs
  have hgc' : HasCompactSupport g' := hgc.comp_left (g := (Complex.ofReal : ℝ → ℂ)) (by simp)
  have hg' : ∀ x, ‖g' x‖≤1 := by
    intro x
    simpa [g',Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg x).1] using (hg x).2
  have hga' : tsupport g' ⊆ Set.Icc (-α) α :=
    (tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) (by simp) g).trans hga
  have hm' : 1-δ < (∫ x : ℝ, ‖g' x‖^2)^(Fintype.card I) := by
    simpa only [g',Complex.norm_real,Real.norm_eq_abs,sq_abs] using hgm
  have hcards : ∀ᶠ B : ℝ in atTop, ∀ i : I,
      ((multiBox B (β i)).card : ℝ)≤(1+δ)*B^(Fintype.card I)*determinant (β i) := by
    rw [Filter.eventually_all]
    exact fun i ↦ multiBox_eventual_card (hβ i) hδ
  have hε : 0<(1+δ)^2-1 := by nlinarith
  have hcoeffs : ∀ᶠ B : ℝ in atTop, ∀ i : I, ∀ u : I → ℤ,
      B^(Fintype.card I)*determinant (β i)*
        ‖∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)‖^2 ≤ (1+δ)^2 := by
    rw [Filter.eventually_all]
    intro i
    simpa only [add_sub_cancel] using tensor_coefficient_eventual hgc' hgs' hg' (hβ i) hε
  have hmasses : ∀ᶠ B : ℝ in atTop, ∀ i : I,
      1-2*δ ≤ ∑ u∈multiBox B (β i), ‖∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)‖^2 := by
    rw [Filter.eventually_all]
    intro i
    exact ((tensor_mass_tendsto hgc' hgs' hg' hα0.le hα hga' (hβ i)).eventually
      (eventually_gt_nhds (by linarith : 1-2*δ<(∫ x : ℝ, ‖g' x‖^2)^(Fintype.card I)))).mono (fun _ h ↦ h.le)
  have hbound := spread_trunc_eventual_bound S c hpoly hgs hgc hg hα0.le hα hga b
    (by intro s hs j; exact hb ⟨s,hs⟩ j) hδ
  obtain ⟨B,hBc,hBs,hBm,hBd,hB⟩ :=
    (hcards.and (hcoeffs.and (hmasses.and (hbound.and (eventually_ge_atTop (1:ℝ)))))).exists
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  let U (i : I) := multiBox B (β i)
  let Q := (i : I) × ↥(U i)
  let J := Fin n ⊕ I
  let A : Q → J → ℤ := fun q ↦ Sum.elim q.1.val q.2.val
  let T (i : I) (u : I → ℤ) : ℂ := ∏ j, (∫ x : ℝ, g' x*phase (B*β i j) (u j) x)
  let C : Q → ℂ := fun q ↦ c q.1.val*T q.1 q.2.val/(1+δ : ℂ)
  let P : ℝ := B^(Fintype.card I)
  have hP : 0<P := pow_pos hB0 _
  let den : ℝ := τ*P*(1+δ)^3
  have hden : 0<den := by dsimp [den]; positivity
  let v : J → ℝ := Sum.elim (fun k ↦ γ k/den) (fun _ ↦ 0)
  have hcurv (q : Q) : (∑ j, (A q j : ℝ)*v j)=f q.1 γ/den := by
    simp only [J,A,v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,mul_zero,
      Finset.sum_const_zero,add_zero,← mul_div_assoc,← Finset.sum_div]
    simp only [f,rowForm_apply]
  have hwidth (q : Q) : |∑ j, (A q j : ℝ)*v j|=ρ q.1/den := by
    rw [hcurv,abs_div,abs_of_pos hden]
  have hC (q : Q) : ‖C q‖^2=‖c q.1.val‖^2*‖T q.1 q.2.val‖^2/(1+δ)^2 := by
    dsimp [C]
    rw [norm_div,norm_mul,div_pow,mul_pow]
    norm_cast
    rw [Real.norm_eq_abs,abs_of_pos hd]
  have hsum : (∑ q : Q, ‖C q‖^2)=
      (∑ i : I, ‖c i.val‖^2*(∑ u∈U i, ‖T i u‖^2))/(1+δ)^2 := by
    simp only [Q,Fintype.sum_sigma,hC]
    simp only [← Finset.sum_div,← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (Finset.sum_subtype (U i) (fun _ ↦ Iff.rfl) (fun u ↦ ‖T i u‖^2)).symm
  have hElo' : 1-δ≤2*∑ i : I, ‖c i.val‖^2 := by
    simpa only [← Finset.sum_coe_sort S] using hElo
  have hEhi' : 2*∑ i : I, ‖c i.val‖^2≤1 := by
    simpa only [← Finset.sum_coe_sort S] using hEhi
  have helo : (1-3*δ)^2≤2*∑ q : Q, ‖C q‖^2 := by
    have h2 : 0≤1-2*δ := by linarith
    have hterm : (∑ i : I, ‖c i.val‖^2)*(1-2*δ)≤∑ i : I, ‖c i.val‖^2*(∑ u∈U i, ‖T i u‖^2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hBm i) (sq_nonneg _)
    have he := mul_le_mul_of_nonneg_right hElo' h2
    rw [hsum]
    apply (spread_numeric_energy hδ hδ20).trans
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith only [hterm,he]) (sq_nonneg _)
  have hwterm (i : I) : ((U i).card : ℝ)*(ρ i/den)≤‖c i.val‖^2/(1+δ) := by
    apply spread_numeric_width hδ hτ hP (hρ i)
    · simpa only [determinant,β,mul_div_assoc] using (hdet i).2
    · exact hBc i
  have hwsum : 2*(∑ q : Q, |∑ j, (A q j : ℝ)*v j|)≤1/(1+δ) := by
    simp only [hwidth,Q,Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,Fintype.card_coe]
    calc
      _ ≤ 2*(∑ i : I, ‖c i.val‖^2/(1+δ)) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hwterm i)) (by norm_num)
      _ = (2*∑ i : I, ‖c i.val‖^2)/(1+δ) := by rw [← Finset.sum_div]; ring
      _ ≤ 1/(1+δ) := div_le_div_of_nonneg_right hEhi' hd.le
  have hsup (y : J → UnitAddCircle) :
      ‖(∑ q : Q, C q*mFourier (A q) y)+conj (∑ q : Q, C q*mFourier (A q) y)‖≤1 := by
    let Z : ℂ := ∑ s∈S, c s*mFourier s (y ∘ Sum.inl)*
      ∏ j : I, rowTrunc g' B (rowForm s (b j)) (y (Sum.inr j))
    have hZ : ‖Z+conj Z‖≤1+δ := hBd (y ∘ Sum.inl) (y ∘ Sum.inr)
    have he : (∑ q : Q, C q*mFourier (A q) y)=Z/(1+δ : ℂ) := by
      rw [Fintype.sum_sigma]
      have hi (i : I) : (∑ u : U i, C ⟨i,u⟩*mFourier (A ⟨i,u⟩) y)=
          (c i.val*mFourier i.val (y ∘ Sum.inl)*(∏ j : I, rowTrunc g' B (β i j) (y (Sum.inr j))))/(1+δ : ℂ) := by
        rw [tensor_trunc_expand]
        change (∑ u : U i, (c i.val*T i u.val/(1+δ : ℂ))*mFourier (Sum.elim i.val u.val) y)=_
        simp only [mFourier_sum_type,Finset.mul_sum,Finset.sum_div]
        rw [← Finset.sum_coe_sort (U i)]
        apply Finset.sum_congr rfl
        intro u _
        dsimp [T, Function.comp_def]
        ring
      simp_rw [hi]
      rw [← Finset.sum_div]
      congr 1
      simpa only [Z,β,f] using Finset.sum_coe_sort S
        (fun s ↦ c s*mFourier s (y ∘ Sum.inl)*∏ j : I, rowTrunc g' B (rowForm s (b j)) (y (Sum.inr j)))
    rw [he,map_div₀,map_add,map_one,conj_ofReal,← add_div,norm_div]
    have he' : ‖(1:ℂ)+(δ:ℂ)‖=1+δ := by
      rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    rw [he',div_le_one hd]
    exact hZ
  have hQ : Nonempty Q := by
    let i : I := Classical.choice inferInstance
    have hu : (0 : I → ℤ)∈U i := by
      simp only [U,multiBox,Fintype.mem_piFinset,Pi.zero_apply,mem_box,Int.cast_zero,abs_zero]
      intro j
      positivity
    exact ⟨⟨i,⟨0,hu⟩⟩⟩
  refine ⟨⟨Q,J,inferInstance,inferInstance,hQ,⟨A,C,v,?_,?_,hsup,helo,?_,?_,?_⟩⟩⟩
  · intro q hz
    apply primitive_ne_zero (positive_primitive (hS q.1.val q.1.property))
    funext k
    exact congrFun hz (Sum.inl k)
  · rintro ⟨s,u⟩ ⟨t,w⟩ hne a ha
    have hh := positive_parallel_eq (hS s.val s.property) (hS t.val t.property)
      (fun k ↦ ha (Sum.inl k))
    have hst : s=t := Subtype.ext hh.1
    subst t
    have huw : u=w := by
      apply Subtype.ext
      funext j
      have hj := ha (Sum.inr j)
      change (u.val j : ℝ)=a*(w.val j : ℝ) at hj
      rw [hh.2,one_mul] at hj
      exact_mod_cast hj
    exact hne (by rw [huw])
  · intro q
    rw [hcurv]
    exact div_ne_zero (hγ q.1) hden.ne'
  · apply hwsum.trans_lt
    exact (div_lt_one hd).mpr (by linarith)
  · intro q
    rw [hC,hwidth]
    apply spread_numeric_coefficient hδ hδ1 hτ hP (hρ q.1) (sq_nonneg _) (sq_nonneg _)
    · simpa only [determinant,β,mul_div_assoc] using (hdet q.1).1
    · exact hBs q.1 q.2.val

end
end AsymptoticallyMinimalLittlewood.Auxiliary

end OAI
