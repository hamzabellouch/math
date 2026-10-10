import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteCoverSums
import OAI.Probability.CriticalPercolation.Harmonic.FiniteHilbert

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma inverse_neighbor_sum (f : FH X) :
    (Function.support (fun y => (W.degree:ℝ)⁻¹*∑ z∈W.neighbors y, f z)).Finite := by
  apply (f.support.biUnion W.neighbors).finite_toSet.subset
  intro y hy
  have hz : (∑ z∈W.neighbors y, f z)≠0 := by
    intro h; apply hy; change (W.degree:ℝ)⁻¹*(∑ z∈W.neighbors y, f z)=0; rw [h,mul_zero]
  obtain ⟨z,hz,hfz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  exact Finset.mem_biUnion.mpr ⟨z,(f.mem_support z).mpr hfz,
    W.mem_neighbors.mpr (W.mem_neighbors.mp hz).symm⟩

def averaging : FH X →ₗ[ℝ] FH X where
  toFun f := FH.ofFunction (fun x => (W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y)
    (W.inverse_neighbor_sum f)
  map_add' f g := by
    ext x
    simp only [FH.ofFunction_apply,FH.add_apply,Finset.sum_add_distrib,mul_add]
  map_smul' c f := by
    ext x
    simp only [FH.ofFunction_apply,FH.smul_apply,←Finset.mul_sum,RingHom.id_apply]
    ring

lemma averaging_coordinate (f : FH X) (x : X) :
    W.averaging f x=(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y := rfl

lemma averaging_delta (x : X) : W.averaging (FH.delta x)=
    (W.degree:ℝ)⁻¹ • ∑ y∈W.neighbors x, FH.delta y := by
  ext z
  simp only [W.averaging_coordinate,FH.smul_apply,FH.sum_apply,FH.delta_apply,
    Finset.sum_ite_eq,Finset.sum_ite_eq',W.mem_neighbors]
  congr 1
  congr 1
  exact propext (W.graph.adj_comm _ _)

lemma averaging_symmetric_delta (x : X) (f : FH X) :
    inner ℝ (W.averaging (FH.delta x)) f=inner ℝ (FH.delta x) (W.averaging f) := by
  rw [W.averaging_delta,(real_inner_smul_left (F:=FH X)),sum_inner,FH.delta_inner]
  simp only [FH.delta_inner,W.averaging_coordinate]

lemma averaging_symmetric (f g : FH X) : inner ℝ (W.averaging f) g=inner ℝ f (W.averaging g) := by
  calc
    _ = inner ℝ (W.averaging (∑ x∈f.support, f x • FH.delta x)) g := by rw [f.delta_decomposition]
    _ = ∑ x∈f.support, f x*inner ℝ (W.averaging (FH.delta x)) g := by
      simp only [map_sum,map_smul,sum_inner,(real_inner_smul_left (F:=FH X))]
    _ = inner ℝ (∑ x∈f.support, f x • FH.delta x) (W.averaging g) := by
      simp only [sum_inner,(real_inner_smul_left (F:=FH X)),W.averaging_symmetric_delta]
    _ = _ := by rw [f.delta_decomposition]

lemma sum_neighbor_sq_bound (F : Finset X) (f : FH X) :
    (∑ x∈F, ∑ y∈W.neighbors x, (f y)^2)≤(W.degree:ℝ)*‖f‖^2 := by
  let J := F.biUnion W.neighbors
  have hof : ∀ y∈J, (F.filter (fun x => y∈W.neighbors x)).card≤W.degree := by
    intro y hy
    calc
      _ ≤ (W.neighbors y).card := Finset.card_le_card (by
        intro x hx
        exact W.mem_neighbors.mpr (W.mem_neighbors.mp (Finset.mem_filter.mp hx).2).symm)
      _ = _ := W.neighbors_card y
  have hh := sum_le_sum_of_finite_overlap F W.neighbors J
    (fun x hx y hy => Finset.mem_biUnion.mpr ⟨x,hx,hy⟩) W.degree hof
    (fun y => (f y)^2) (fun y => sq_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_left (f.sum_sq_le_norm_sq J) (Nat.cast_nonneg _))

lemma averaging_norm_le (hD : 0<W.degree) (f : FH X) : ‖W.averaging f‖≤‖f‖ := by
  have hD' : (0:ℝ)<W.degree := by exact_mod_cast hD
  have hpoint (x : X) : (W.averaging f x)^2≤(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, (f y)^2 := by
    have hh := sq_sum_le_card_mul_sum_sq (s:=W.neighbors x) (f:=fun y => f y)
    rw [W.neighbors_card] at hh
    rw [W.averaging_coordinate,mul_pow]
    have he : (W.degree:ℝ)⁻¹^2*(W.degree:ℝ)=(W.degree:ℝ)⁻¹ := by field_simp
    calc
      _ ≤ (W.degree:ℝ)⁻¹^2*((W.degree:ℝ)*∑ y∈W.neighbors x, (f y)^2) :=
        mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = _ := by rw [←mul_assoc,he]
  have hsum := Finset.sum_le_sum (fun x (_ : x∈(W.averaging f).support) => hpoint x)
  rw [←(W.averaging f).norm_sq_eq_sum _ (Finset.Subset.refl _),←Finset.mul_sum] at hsum
  have hbound := mul_le_mul_of_nonneg_left (W.sum_neighbor_sq_bound (W.averaging f).support f)
    (inv_nonneg.mpr hD'.le)
  rw [←mul_assoc,inv_mul_cancel₀ hD'.ne',one_mul] at hbound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsum.trans hbound)

def lazyWalk : FH X →ₗ[ℝ] FH X := (1/2:ℝ) • (LinearMap.id+W.averaging)
def walkEnergy (f : FH X) : ℝ := inner ℝ f (f-W.lazyWalk f)
lemma lazyWalk_apply (f : FH X) : W.lazyWalk f=(1/2:ℝ) • (f+W.averaging f) := rfl

lemma lazyWalk_coordinate (f : FH X) (x : X) : W.lazyWalk f x=
    (1/2:ℝ)*(f x+(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y) := rfl

lemma lazyWalk_symmetric (f g : FH X) :
    inner ℝ (W.lazyWalk f) g=inner ℝ f (W.lazyWalk g) := by
  simp only [W.lazyWalk_apply,(real_inner_smul_left (F:=FH X)),(real_inner_smul_right (F:=FH X)),
    inner_add_left,inner_add_right,W.averaging_symmetric]
lemma lazyWalk_norm_le (hD : 0<W.degree) (f : FH X) : ‖W.lazyWalk f‖≤‖f‖ := by
  rw [W.lazyWalk_apply,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have ht := norm_add_le f (W.averaging f)
  have ha := W.averaging_norm_le hD f
  linarith
lemma lazyWalk_positive (hD : 0<W.degree) (f : FH X) : 0 ≤ inner ℝ f (W.lazyWalk f) := by
  have hb := abs_real_inner_le_norm f (W.averaging f)
  have h := mul_le_mul_of_nonneg_left (W.averaging_norm_le hD f) (norm_nonneg f)
  have hl := (abs_le.mp (hb.trans h)).1
  simp only [W.lazyWalk_apply,(real_inner_smul_right (F:=FH X)),inner_add_right,real_inner_self_eq_norm_sq]
  nlinarith
lemma walkEnergy_nonneg (hD : 0<W.degree) (f : FH X) : 0≤W.walkEnergy f := by
  have hb := real_inner_le_norm f (W.lazyWalk f)
  have h := mul_le_mul_of_nonneg_left (W.lazyWalk_norm_le hD f) (norm_nonneg f)
  unfold walkEnergy
  rw [inner_sub_right,real_inner_self_eq_norm_sq]
  nlinarith
lemma walkEnergy_dissipation (hD : 0<W.degree) (f : FH X) :
    ‖f-W.lazyWalk f‖^2≤W.walkEnergy f-W.walkEnergy (W.lazyWalk f) := by
  have hp := W.lazyWalk_positive hD (f-W.lazyWalk f)
  rw [map_sub] at hp
  simp only [inner_sub_left,inner_sub_right] at hp
  rw [←W.lazyWalk_symmetric f (W.lazyWalk f)] at hp
  have hcomm : inner ℝ (W.lazyWalk f) f=inner ℝ f (W.lazyWalk f) := real_inner_comm _ _
  unfold walkEnergy
  simp only [inner_sub_right,real_inner_self_eq_norm_sq,norm_sub_sq_real]
  nlinarith [real_inner_self_eq_norm_sq (W.lazyWalk f)]

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
