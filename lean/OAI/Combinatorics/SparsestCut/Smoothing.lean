import OAI.Combinatorics.SparsestCut.CellInterface

namespace OAI

universe u1 u2 u3

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductSlice
open MeasureTheory Set CellInterface
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {A : Type u3} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype A] [DecidableEq I]

def ell (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (i : I) : (ℝ × Z) →L[ℝ] ℝ :=
  pivot i • form (B i)
omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype I] [DecidableEq I] in
@[simp] lemma ell_apply (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (i : I) (x : ℝ × Z) :
    ell B pivot i x=pivot i*(x.1-B i x.2) := rfl

omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype I] [DecidableEq I] in
lemma normalized_ell (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (i : I) (k : ℤ) (x : ℝ × Z) :
    (ell B pivot i x-(k:ℝ)*τ)/pivot i=form (B i) x-(k:ℝ)*τ/pivot i := by
  simp only [ell,_root_.smul_apply,smul_eq_mul,sub_div,mul_div_cancel_left₀ _ (hp i)]

omit [Fintype A] [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [DecidableEq I] in
lemma cell_eq_extension (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z)) (F : LabelVertex (ell B pivot) τ U → A → ℝ)
    (x : ℝ × Z) (α : A) :
    cell B (fun i (k : s) => -((k:ℤ)*τ/pivot i))
      (fun P => extension (ell B pivot) pivot τ s U F P α) x =
    extension (ell B pivot) pivot τ s U F (pattern (ell B pivot) pivot τ s x) α := by
  unfold cell pattern
  simp_rw [normalized_ell B pivot hp]
  simp only [sub_eq_add_neg]

def eventPoint (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ)
    (θ : ℝ × Z) (i : I) (k : ℤ) (z : Z) : ℝ × Z :=
  θ-(form (B i) θ+B i z-(k:ℝ)*τ/pivot i,z)

omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype I] [DecidableEq I] in
lemma event_form (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ)
    (θ : ℝ × Z) (i : I) (k : ℤ) (z : Z) (j : I) :
    form (B j) (eventPoint B pivot τ θ i k z) =
      form (B j) θ+B j z-(form (B i) θ+B i z-(k:ℝ)*τ/pivot i) := by
  simp only [eventPoint,form_apply,map_sub]
  ring
omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype I] [DecidableEq I] in
lemma event_on_plane (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (θ : ℝ × Z) (i : I) (k : ℤ) (z : Z) :
    ell B pivot i (eventPoint B pivot τ θ i k z)=(k:ℝ)*τ := by
  change pivot i*form (B i) _=_
  rw [event_form]
  field_simp [hp i]
  ring

lemma event_other_regular (B : I → Z →L[ℝ] ℝ) (hB : Function.Injective B)
    (pivot : I → ℝ) (hp : ∀ i, pivot i≠0) (τ : ℝ) (θ : ℝ × Z) (i : I) (k : ℤ)
    (μ : Measure Z) (hμ : μ ≪ volume) :
    ∀ᵐ z ∂μ, ∀ j, j≠i → ∀ l : ℤ, ell B pivot j (eventPoint B pivot τ θ i k z)≠(l:ℝ)*τ := by
  apply ae_all_iff.mpr
  intro j
  by_cases hj : j=i
  · simp [hj]
  have hpair (l : ℤ) : ∀ᵐ z ∂μ, ell B pivot j (eventPoint B pivot τ θ i k z)≠(l:ℝ)*τ := by
    have hn : B j-B i≠0 := sub_ne_zero.mpr (fun he => hj (hB he))
    let t := (l:ℝ)*τ/pivot j-(k:ℝ)*τ/pivot i-form (B j) θ+form (B i) θ
    have hnul := SliceCoefficients.affine_hyperplane_null (B j-B i) hn t volume
    have hae : ∀ᵐ z ∂volume, (B j-B i) z≠t := by rw [ae_iff]; simpa only [not_not] using hnul
    filter_upwards [hμ.ae_le hae] with z hz he
    apply hz
    change pivot j*form (B j) _=_ at he
    rw [event_form] at he
    have he' : form (B j) θ+B j z-(form (B i) θ+B i z-(k:ℝ)*τ/pivot i)=(l:ℝ)*τ/pivot j :=
      (eq_div_iff (hp j)).mpr (by nlinarith [he])
    simp only [_root_.sub_apply]
    dsimp only [t]
    linarith
  filter_upwards [ae_all_iff.mpr hpair] with z hz _ using hz

omit [Fintype A] [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [DecidableEq I] in
lemma jump_eq_traces (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z)) (F : LabelVertex (ell B pivot) τ U → A → ℝ)
    (θ : ℝ × Z) (i : I) (k : s) (z : Z) (α : A) :
    jump B (fun i (k : s) => -((k:ℤ)*τ/pivot i))
      (extension (ell B pivot) pivot τ s U F) θ i k z α =
    extension (ell B pivot) pivot τ s U F
      (weakPattern (ell B pivot) pivot τ s (eventPoint B pivot τ θ i k.val z)) α-
    extension (ell B pivot) pivot τ s U F
      (pattern (ell B pivot) pivot τ s (eventPoint B pivot τ θ i k.val z)) α := by
  unfold jump weakPattern pattern
  congr 2 <;> apply Finset.filter_congr <;> intro p _ <;>
    rw [normalized_ell B pivot hp,event_form] <;> constructor <;> intro h <;> linarith

lemma actual_jump_budget (B : I → Z →L[ℝ] ℝ) (hB : Function.Injective B)
    (pivot : I → ℝ) (hp : ∀ i, pivot i≠0) {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ)
    {U : Set (ℝ × Z)} (hU : IsOpen U)
    (hb : ∀ x∈U, regular (ell B pivot) τ x → ∀ i, label (ell B pivot) τ x i∈s)
    (F : LabelVertex (ell B pivot) τ U → A → ℝ) {J : ℝ}
    (hF : ∀ (vp vm : LabelVertex (ell B pivot) τ U) (i : I), vp.val i=vm.val i+1 →
      (∀ j, j≠i → vp.val j=vm.val j) → ∑ a, |F vp a-F vm a|≤J)
    (φ : ℝ → ℝ) (ψ : Z → ℝ) (θ : ℝ × Z) (i : I)
    (hsupp : ∀ᵐ z ∂law ψ volume, ∀ k : s,
      φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)≠0 → eventPoint B pivot τ θ i k.val z∈U) :
    ∀ᵐ z ∂law ψ volume, ∀ k : s,
      φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)≠0 →
        ∑ a, |jump B (fun i (k : s) => -((k:ℤ)*τ/pivot i))
          (extension (ell B pivot) pivot τ s U F) θ i k z a|≤J := by
  have hae := ae_all_iff.mpr (fun k : s => event_other_regular B hB pivot hp τ θ i k.val _ (law_ac ψ volume))
  filter_upwards [hsupp,hae] with z hz hreg k hk
  simp_rw [jump_eq_traces B pivot hp]
  apply interface_jump_bound (ell B pivot) pivot hp hτ s hU hb F hF (hz k hk) i k.val
    (event_on_plane B pivot hp τ θ i k.val z) (hreg k) (pivot i,0)
  simp only [ell_apply,map_zero,sub_zero]
  exact mul_self_pos.mpr (hp i)

end
end UniformSparsestCut.ProductSlice

end

end OAI
