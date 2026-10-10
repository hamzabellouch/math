import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.NuclearDefinition
import OAI.Analysis.JiangSu.TensorProducts.FaithfulTensorCrossNorm
import OAI.Analysis.JiangSu.CStarAlgebras.ApproximateUnitSequence

namespace OAI

section

noncomputable section
namespace NuclearUnitization
open Pureness Filter Topology
open scoped TensorProduct

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] {B : Type v} [CStarAlgebra B]

def restrictNorm (p : CStarAlgebraNorm ((Unitization ℂ A) ⊗[ℂ] B)) : NonUnitalCStarNorm (A ⊗[ℂ] B) where
  toFun x := p.toAlgebraNorm (tensorInr x)
  map_zero' := by simp
  add_le' x y := by simpa only [map_add] using map_add_le_add p.toAlgebraNorm (tensorInr x) (tensorInr y)
  neg' x := by simp
  mul_le' x y := by simpa only [map_mul] using map_mul_le_mul p.toAlgebraNorm (tensorInr x) (tensorInr y)
  eq_zero_of_map_eq_zero' x hx := (tensorInr_injective (A := A) (B := B)) (by simpa using p.toAlgebraNorm.eq_zero_of_map_eq_zero' _ hx)
  smul c x := by
    change p.toAlgebraNorm (tensorInr (c • x))=‖c‖*p.toAlgebraNorm (tensorInr x)
    rw [map_smul]
    exact p.toAlgebraNorm.smul' c (tensorInr x)
  cstar x := by
    change p.toAlgebraNorm (tensorInr (star x*x))=p.toAlgebraNorm (tensorInr x)*p.toAlgebraNorm (tensorInr x)
    rw [map_mul,map_star,p.cstar]

lemma nuclear_restriction_eq (hA : IsNuclear.{u,v} A)
    (p q : CStarAlgebraNorm ((Unitization ℂ A) ⊗[ℂ] B)) (w : A ⊗[ℂ] B) :
    p.toAlgebraNorm (tensorInr w)=q.toAlgebraNorm (tensorInr w) := by
  exact congrArg (fun r : NonUnitalCStarNorm (A ⊗[ℂ] B) => r.toRingNorm w)
    ((hA B).elim (restrictNorm p) (restrictNorm q))

variable [PartialOrder A] [StarOrderedRing A]

lemma norm_one_sub_inr {a : A} (ha : 0≤a) (hn : ‖a‖≤1) : ‖1-(Unitization.inr a : Unitization ℂ A)‖=1 := by
  have hip : 0≤(Unitization.inr a : Unitization ℂ A) := map_nonneg (Unitization.inrNonUnitalStarAlgHom ℂ A) ha
  have hin : (Unitization.inr a : Unitization ℂ A)≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hip).mp (by simpa only [Unitization.norm_inr] using hn)
  apply le_antisymm
  · apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hin)).mpr
    exact sub_le_self _ hip
  · rw [Unitization.norm_eq_sup]
    exact (by simp only [sub_eq_add_neg,Unitization.fst_add,Unitization.fst_one,Unitization.fst_neg,Unitization.fst_inr,neg_zero,add_zero,norm_one] : (1 : ℝ) = ‖(1-(Unitization.inr a : Unitization ℂ A)).fst‖).le.trans (le_max_left _ _)

omit [PartialOrder A] [StarOrderedRing A] in
lemma tensor_approx_unit_defect
    (p : CStarAlgebraNorm ((Unitization ℂ A) ⊗[ℂ] B))
    (e : ℕ → A) (he : ∀ a : A, Tendsto (fun n => e n*a) atTop (𝓝 a)) (w : A ⊗[ℂ] B) :
    Tendsto (fun n => p.toAlgebraNorm (((1-(Unitization.inr (e n) : Unitization ℂ A)) ⊗ₜ[ℂ] (1 : B))*tensorInr w)) atTop (𝓝 0) := by
  suffices hh : Tendsto (fun n => p.completionMap (((1-(Unitization.inr (e n) : Unitization ℂ A)) ⊗ₜ[ℂ] (1 : B))*tensorInr w)) atTop (𝓝 0) by
    simpa only [p.completionMap_norm,norm_zero] using hh.norm
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add,mul_add,add_zero] using hx.add hy
  | tmul a b =>
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn (n : ℕ) : ‖p.completionMap (((1-(Unitization.inr (e n) : Unitization ℂ A)) ⊗ₜ[ℂ] (1 : B))*tensorInr (a ⊗ₜ[ℂ] b))‖ = ‖a-e n*a‖*‖b‖ := by
      rw [p.completionMap_norm,tensorInr_tmul,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
      have hd : (1-(Unitization.inr (e n) : Unitization ℂ A))*Unitization.inr a=Unitization.inr (a-e n*a) := by
        simp [sub_mul]
      rw [hd,cstar_norm_tmul,Unitization.norm_inr]
    simp_rw [hn]
    simpa only [sub_self,norm_zero,zero_mul] using ((tendsto_const_nhds (x := a)).sub (he a)).norm.mul_const ‖b‖

lemma scalar_part_bound [TopologicalSpace.SeparableSpace A]
    (p : CStarAlgebraNorm ((Unitization ℂ A) ⊗[ℂ] B)) (w : A ⊗[ℂ] B) (b : B) :
    ‖b‖≤p.toAlgebraNorm (tensorInr w+(1 : Unitization ℂ A) ⊗ₜ[ℂ] b) := by
  obtain ⟨e,hep,hen,he⟩ := SequentialApproximateUnit.exists_sequence (A := A)
  let z := tensorInr w+(1 : Unitization ℂ A) ⊗ₜ[ℂ] b
  let E (n : ℕ) := (1-(Unitization.inr (e n) : Unitization ℂ A)) ⊗ₜ[ℂ] (1 : B)
  have hlim := tensor_approx_unit_defect p e (fun a => (he a).1) w
  have hb (n : ℕ) : ‖b‖≤p.toAlgebraNorm z+p.toAlgebraNorm (E n*tensorInr w) := by
    have hn : p.toAlgebraNorm (E n)≤1 := by
      dsimp only [E]
      rw [cstar_norm_tmul,norm_one_sub_inr (hep n) (hen n),one_mul]
      by_cases hB : Nontrivial B
      · let _ := hB; exact (norm_one (α := B)).le
      · let _ := not_nontrivial_iff_subsingleton.mp hB
        simp [Subsingleton.elim (1 : B) 0]
    have hd : (1-(Unitization.inr (e n) : Unitization ℂ A)) ⊗ₜ[ℂ] b=E n*z-E n*tensorInr w := by
      simp [z,E,mul_add]
    calc
      ‖b‖ = p.toAlgebraNorm ((1-(Unitization.inr (e n) : Unitization ℂ A)) ⊗ₜ[ℂ] b) := by rw [cstar_norm_tmul,norm_one_sub_inr (hep n) (hen n),one_mul]
      _ ≤ p.toAlgebraNorm (E n*z)+p.toAlgebraNorm (E n*tensorInr w) := by rw [hd]; exact map_sub_le_add _ _ _
      _ ≤ p.toAlgebraNorm z+p.toAlgebraNorm (E n*tensorInr w) := by
        gcongr
        exact (map_mul_le_mul p.toAlgebraNorm _ _).trans
          (mul_le_of_le_one_left (apply_nonneg _ _) hn)
  have hl : Tendsto (fun n => p.toAlgebraNorm z+p.toAlgebraNorm (E n*tensorInr w)) atTop (𝓝 (p.toAlgebraNorm z)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hlim
  exact ge_of_tendsto' hl hb

lemma nuclear_norm_bound [TopologicalSpace.SeparableSpace A]
    (hA : IsNuclear.{u,v} A) (p q : CStarAlgebraNorm ((Unitization ℂ A) ⊗[ℂ] B))
    (z : (Unitization ℂ A) ⊗[ℂ] B) : p.toAlgebraNorm z≤3*q.toAlgebraNorm z := by
  obtain ⟨w,b,hz⟩ := tensor_split z
  have hw : tensorInr w=z-(1 : Unitization ℂ A) ⊗ₜ[ℂ] b := by rw [hz]; abel
  have hb : ‖b‖≤q.toAlgebraNorm z := hz ▸ scalar_part_bound q w b
  have h1 : p.toAlgebraNorm z≤p.toAlgebraNorm (tensorInr w)+‖b‖ := by
    rw [hz]
    exact (map_add_le_add p.toAlgebraNorm _ _).trans (by rw [cstar_norm_tmul,norm_one,one_mul])
  rw [nuclear_restriction_eq hA p q,hw] at h1
  have h2 : q.toAlgebraNorm (z-(1 : Unitization ℂ A) ⊗ₜ[ℂ] b)≤q.toAlgebraNorm z+‖b‖ := by
    exact (map_sub_le_add q.toAlgebraNorm _ _).trans (by rw [cstar_norm_tmul,norm_one,one_mul])
  linarith

theorem nuclear_unitization [TopologicalSpace.SeparableSpace A]
    (hA : IsNuclear.{u,v} A) : Pureness.IsNuclear.{u,v} (Unitization ℂ A) := by
  intro B _
  refine ⟨fun p q => CStarAlgebraNorm.eq_of_mutual_bound p q
    ⟨3,nuclear_norm_bound hA p q⟩ ⟨3,nuclear_norm_bound hA q p⟩⟩

end NuclearUnitization

end
end

end OAI
