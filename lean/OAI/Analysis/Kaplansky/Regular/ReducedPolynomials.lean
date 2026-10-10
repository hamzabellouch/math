import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.ReducedTrace

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]
abbrev Op (G : Type*) [Group G] := HilbertSum G ℂ →L[ℂ] HilbertSum G ℂ

def polynomial : (G →₀ ℂ) →ₗ[ℂ] Algebra G := Finsupp.linearCombination ℂ generator
lemma polynomial_apply (c : G →₀ ℂ) :
    (polynomial c).val = ∑ g ∈ c.support, c g • left g := by
  simp only [polynomial,Finsupp.linearCombination_apply,Finsupp.sum]
  change (Algebra G).subtype (∑ g ∈ c.support, c g • generator g) = _
  simp only [map_sum,map_smul]
  rfl

lemma span_left_mul {x y : Op G}
    (hx : x ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ))))
    (hy : y ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ)))) :
    x*y ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ))) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h,rfl⟩ := hy
      rw [←left_mul]
      exact Submodule.subset_span ⟨g*h,rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [mul_add] using (Submodule.span ℂ _).add_mem ihx ihy
    | smul c x hx ih => simpa only [mul_smul_comm] using (Submodule.span ℂ _).smul_mem c ih
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [add_mul] using (Submodule.span ℂ _).add_mem ihx ihy
  | smul c x hx ih => simpa only [smul_mul_assoc] using (Submodule.span ℂ _).smul_mem c ih

lemma span_left_star {x : Op G}
    (hx : x ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ)))) :
    star x ∈ Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ))) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    rw [left_star]
    exact Submodule.subset_span ⟨g⁻¹,rfl⟩
  | zero =>
    rw [star_zero (Op G)]
    exact (Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ)))).zero_mem
  | add x y hx hy ihx ihy =>
    rw [star_add x y]
    exact (Submodule.span ℂ _).add_mem ihx ihy
  | smul c x hx ih => simpa only [star_smul] using (Submodule.span ℂ _).smul_mem (star c) ih

def polynomialAlgebra : StarSubalgebra ℂ (Op G) where
  carrier := Submodule.span ℂ (Set.range (left (G:=G) (H:=ℂ)))
  zero_mem' := (Submodule.span ℂ _).zero_mem
  one_mem' := by
    rw [←left_one (G:=G) (H:=ℂ)]
    exact Submodule.subset_span ⟨1,rfl⟩
  add_mem' := (Submodule.span ℂ _).add_mem
  mul_mem' := span_left_mul
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one,←left_one (G:=G) (H:=ℂ)]
    exact (Submodule.span ℂ _).smul_mem c (Submodule.subset_span ⟨1,rfl⟩)
  star_mem' := span_left_star

lemma adjoin_left_le_polynomial :
    StarAlgebra.adjoin ℂ (Set.range (left (G:=G) (H:=ℂ))) ≤ polynomialAlgebra := by
  apply StarAlgebra.adjoin_le
  exact Submodule.subset_span

lemma polynomial_dense (x : Algebra G) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : G →₀ ℂ, ‖x-polynomial c‖ < ε := by
  have hx : x.val ∈ closure (StarAlgebra.adjoin ℂ (Set.range (left (G:=G) (H:=ℂ))) : Set (Op G)) := x.property
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
  have hs := adjoin_left_le_polynomial hy
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hs
  refine ⟨c,?_⟩
  change ‖x.val-(polynomial c).val‖ < ε
  rw [polynomial_apply]
  rw [Finsupp.sum] at hc
  rw [hc]
  simpa only [dist_eq_norm] using hxy

@[simp] lemma coefficient_generator (g : G) : coefficient (generator g) = if g=1 then 1 else 0 := by
  simp [coefficient,generator,delta_apply]

@[simp] lemma coefficient_polynomial (c : G →₀ ℂ) : coefficient (polynomial c) = c 1 := by
  change (canonicalTrace.functional) (polynomial c) = _
  simp only [polynomial,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
  change (∑ g ∈ c.support, c g • coefficient (generator g)) = _
  simp only [coefficient_generator,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp [eq_comm]

lemma coefficient_norm_le (x : Algebra G) : ‖coefficient x‖ ≤ ‖x‖ := by
  have hd : ‖delta (1:G)‖ = 1 := by simp [delta,lp.norm_single]
  rw [coefficient,←inner_delta]
  calc
    _ ≤ ‖delta (1:G)‖ * ‖x.val (delta 1)‖ := norm_inner_le_norm _ _
    _ ≤ ‖delta (1:G)‖ * (‖x.val‖*‖delta 1‖) := mul_le_mul_of_nonneg_left (x.val.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [hd,mul_one,one_mul]; rfl

lemma polynomial_erase (c : G →₀ ℂ) :
    polynomial (c.erase 1) = polynomial c - c 1 • (1:Algebra G) := by
  rw [Finsupp.erase_eq_sub_single,map_sub]
  congr 1
  simp only [polynomial,Finsupp.linearCombination_single]
  congr 1
  apply Subtype.ext
  exact left_one

lemma polynomial_dense_zero (x : Algebra G) (hx : coefficient x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : G →₀ ℂ, c 1=0 ∧ ‖x-polynomial c‖ < ε := by
  obtain ⟨c,hc⟩ := polynomial_dense x (ε/2) (half_pos hε)
  have hcoeff : ‖c 1‖ ≤ ‖x-polynomial c‖ := by
    have h := coefficient_norm_le (x-polynomial c)
    change ‖canonicalTrace.functional (x-polynomial c)‖ ≤ _ at h
    simp only [map_sub] at h
    change ‖coefficient x-coefficient (polynomial c)‖ ≤ _ at h
    simpa only [hx,coefficient_polynomial,zero_sub,norm_neg] using h
  refine ⟨c.erase 1,Finsupp.erase_same,?_⟩
  rw [polynomial_erase]
  calc
    _ = ‖(x-polynomial c)+c 1•(1:Algebra G)‖ := by congr 1; abel
    _ ≤ ‖x-polynomial c‖+‖c 1•(1:Algebra G)‖ := norm_add_le _ _
    _ ≤ ‖x-polynomial c‖+‖c 1‖ := by
      gcongr
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by change ‖(1:Op G)‖ ≤ 1; exact ContinuousLinearMap.norm_id_le)
    _ < _ := by linarith


end KaplanskyConsequences.Regular

end

end OAI
