import OAI.Combinatorics.SparsestCut.CoordinateSplit

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.EuclideanCells
open MeasureTheory Set ProductSlice CellInterface CoordinateSplit
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} {I : Type u1} {A : Type u2} [Fintype I] [Fintype A] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

def B (u : I → E) : I → Z →L[ℝ] ℝ := fun i => slope (u i)
def pivot (u : I → E) (i : I) : ℝ := u i 0

def values (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) : Finset (I × s) → A → ℝ :=
  extension (ell (B u) (pivot u)) (pivot u) τ s U F

def chartFunction (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) (a : A) : E → ℝ :=
  (cell (B u) (fun i (k : s) => -((k:ℤ)*τ/pivot u i)) (fun P => values u τ s U F P a)) ∘ split

lemma form_comp (u : E) (hu : u 0≠0) :
    (form (slope u)).comp split.toContinuousLinearMap=(u 0)⁻¹ • InnerProductSpace.toDual ℝ E u := by
  ext x
  have hh := normalized_form u hu x
  change (split x).1-slope u (split x).2=(u 0)⁻¹*inner ℝ u x
  rw [← hh,div_eq_mul_inv,mul_comm]

lemma kernel_split (φ : ℝ → ℝ) :
    (ProductMollifier.kernel (m := m+1) φ) ∘ split.symm =
      (fun p : ℝ × Z => φ p.1*ProductMollifier.kernel φ p.2) := by
  funext p
  simp [ProductMollifier.kernel,Fin.prod_univ_succ]

omit [Fintype A] [DecidableEq I] in
lemma chartFunction_eq (u : I → E) (hu : ∀ i, u i 0≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (hb : ∀ x∈U, regular (ell (B u) (pivot u)) τ x → ∀ i, label (ell (B u) (pivot u)) τ x i∈s)
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ)
    (x : E) (hx : split x∈U) (hr : regular (ell (B u) (pivot u)) τ (split x)) (a : A) :
    chartFunction u τ s U F a x=F (vertex (ell (B u) (pivot u)) τ (split x) hx hr) a := by
  change cell (B u) (fun i (k : s) => -((k:ℤ)*τ/pivot u i)) (fun P => extension (ell (B u) (pivot u)) (pivot u) τ s U F P a) (split x)=_
  rw [cell_eq_extension (B u) (pivot u) hu (F := F)]
  exact congrFun (extension_eq (ell (B u) (pivot u)) (pivot u) hu hτ s U hb F _ hx hr) a

omit [Fintype A] in
lemma chartFunction_measurable (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) (a : A) :
    Measurable (chartFunction u τ s U F a) :=
  (cell_measurable _ _ _).comp split.continuous.measurable

omit [Fintype A] in
lemma chartFunction_integrable (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) {M : ℝ} (hM : 0≤M)
    (hF : ∀ v a, |F v a|≤M) (a : A) : LocallyIntegrable (chartFunction u τ s U F a) := by
  apply (locallyIntegrable_const M).mono (chartFunction_measurable _ _ _ _ _ _).aestronglyMeasurable
  filter_upwards with x
  simpa only [chartFunction,Function.comp_apply,cell,values,Real.norm_eq_abs,abs_of_nonneg hM] using extension_bounded _ _ _ _ _ F hM hF _ a

lemma coefficients (u : I → E) (hu : ∀ i, u i 0≠0)
    (hnp : ∀ i j, i≠j → ∀ t : ℝ, u i≠t • u j)
    {τ lam : ℝ} (hτ : 0<τ) (hlam : 0<lam) (s : Finset ℤ)
    {U : Set (ℝ × Z)} (hU : IsOpen U)
    (hb : ∀ x∈U, regular (ell (B u) (pivot u)) τ x → ∀ i, label (ell (B u) (pivot u)) τ x i∈s)
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) {M J : ℝ}
    (hM : 0≤M) (hJ : 0≤J) (hbound : ∀ v a, |F v a|≤M)
    (hF : ∀ (vp vm : LabelVertex (ell (B u) (pivot u)) τ U) (i : I), vp.val i=vm.val i+1 →
      (∀ j, j≠i → vp.val j=vm.val j) → ∑ a, |F vp a-F vm a|≤J)
    (θ : E)
    (hsupp : ∀ᵐ z ∂law (ProductMollifier.kernel (m := m) (ProductMollifier.density lam)) volume,
      ∀ t : ℝ, |t|<lam → split θ-(t,z)∈U)
    (hsmall : ∀ i, τ/|pivot u i| *(lam⁻¹*(∫ t, |deriv ProductMollifier.rho t|))≤1) :
    ∃ β : I → A → ℝ,
      (∀ a, HasFDerivAt (convolution (ProductMollifier.kernel (m := m+1) (ProductMollifier.density lam))
          (chartFunction u τ s U F a) (ContinuousLinearMap.mul ℝ ℝ) volume)
        (∑ i, β i a • InnerProductSpace.toDual ℝ E (u i)) θ) ∧
      (∀ i, ∑ a, |β i a|≤2*J/τ) := by
  let φ := ProductMollifier.density lam
  let ψ : Z → ℝ := ProductMollifier.kernel φ
  let Ξ := values u τ s U F
  let q (i : I) (k : s) := -((k:ℤ)*τ/pivot u i)
  have hBij := slope_injective u hu hnp
  have hq (i : I) : Function.Injective (q i) := by
    intro k l he
    apply Subtype.ext
    have he' : (k.val:ℝ)=(l.val:ℝ) := by
      dsimp only [q] at he
      exact (mul_left_inj' hτ.ne').mp ((div_left_inj' (show pivot u i≠0 from hu i)).mp (neg_injective he))
    exact_mod_cast he'
  have hcφ := (ProductMollifier.density_smooth lam).continuous
  have hiφ := ProductMollifier.density_integrable hlam
  have hcompφ := ProductMollifier.density_compact hlam
  have hdφ (t : ℝ) : HasDerivAt φ (deriv φ t) t :=
    ((ProductMollifier.density_smooth lam).differentiable (by simp) t).hasDerivAt
  have hiφ' : Integrable (deriv φ) :=
    ((ProductMollifier.density_smooth lam).continuous_deriv (by simp)).integrable_of_hasCompactSupport hcompφ.deriv
  have hnφ := ProductMollifier.density_nonneg hlam.le
  have hcψ := ProductMollifier.kernel_smooth (m := m) φ (ProductMollifier.density_smooth lam)
  have hcompψ := ProductMollifier.kernel_compact (m := m) hlam.le (fun t ht => (ProductMollifier.density_support hlam ht).le)
  have hiψ : Integrable ψ := hcψ.continuous.integrable_of_hasCompactSupport hcompψ
  have hnψ := ProductMollifier.kernel_nonneg (m := m) hnφ
  have hψ1 : ∫ z, ψ z=1 := by rw [ProductMollifier.kernel_integral,ProductMollifier.density_integral hlam,one_pow]
  obtain ⟨C,hC⟩ := hcφ.bounded_above_of_compact_support hcompφ
  have hC0 : 0≤C := (norm_nonneg (φ 0)).trans (hC 0)
  have hΞ : ∀ P a, |Ξ P a|≤M := extension_bounded _ _ _ _ _ F hM hbound
  let d (i : I) (a : A) : ℝ := ∑ k : s, ∫ z,
      -(φ (form (B u i) (split θ)+B u i z-(k:ℤ)*τ/pivot u i)*
        jump (B u) q Ξ (split θ) i k z a) ∂law ψ volume
  refine ⟨fun i a => (pivot u i)⁻¹*d i a,?_,?_⟩
  · intro a
    have hd := convolution_derivative (B u) hBij q hq (fun P => Ξ P a) hM hC0 (fun P => hΞ P a)
      hiφ hcφ hC hcψ.continuous.measurable hnψ hiψ hψ1 (split θ)
    have he : convolution (ProductMollifier.kernel (m := m+1) φ) (chartFunction u τ s U F a)
        (ContinuousLinearMap.mul ℝ ℝ) volume =
        (convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell (B u) q (fun P => Ξ P a))
          (ContinuousLinearMap.mul ℝ ℝ) volume) ∘ split := by
      funext x
      rw [chartFunction,convolution_split,kernel_split]
      rfl
    rw [he]
    have hd' : HasFDerivAt
        (convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell (B u) q (fun P => Ξ P a))
          (ContinuousLinearMap.mul ℝ ℝ) volume)
        (∑ i, d i a • form (B u i)) (split θ) := by
      simpa only [d,jump,q,sub_eq_add_neg] using hd
    have ht := derivative_transport _ _ θ hd'
    have hL : (∑ i, d i a • form (B u i)).comp split.toContinuousLinearMap =
        ∑ i, ((pivot u i)⁻¹*d i a) • InnerProductSpace.toDual ℝ E (u i) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      have hi := congrArg (fun L : E →L[ℝ] ℝ => L x) (form_comp (u i) (hu i))
      change form (B u i) (split x)=(pivot u i)⁻¹*inner ℝ (u i) x at hi
      change d i a * form (B u i) (split x)=((pivot u i)⁻¹*d i a)*inner ℝ (u i) x
      rw [hi]
      ring
    rw [hL] at ht
    exact ht
  · intro i
    have hj := actual_jump_budget (B u) hBij (pivot u) hu hτ s hU hb F hF φ ψ (split θ) i (by
      filter_upwards [hsupp] with z hz k hk
      exact hz _ (ProductMollifier.density_support hlam hk))
    have hh := common_coefficient_budget (B u) s (pivot u) hu hτ Ξ hM hC0 hJ hΞ
      hdφ hnφ hiφ hiφ' (ProductMollifier.density_integral hlam) hC
      hcψ.continuous.measurable hnψ hiψ hψ1 (split θ) i hj (by
        rw [ProductMollifier.density_deriv_integral hlam]
        exact hsmall i)
    exact hh
end
end UniformSparsestCut.EuclideanCells

end

end OAI
