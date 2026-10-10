import Mathlib
import OAI.Geometry.Borsuk.SphereGeometry.TraceSphere
import OAI.Geometry.Borsuk.Simplicial.OddHomotopySurjective

namespace OAI

namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator
open SimplicialChains
section TraceHomotopy
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
local notation "D" => EuclideanSpace ℝ (UpperTriangle ν)
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι

omit [Nonempty ν] in
lemma Admissible.traceHomotopy_ray {f : EuclideanSpace ℝ ν → ι → ℝ} (_hf : Admissible f)
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (G : ℝ × traceSphere ν → Y)
    (hG : ContinuousOn G (Set.Icc (0:ℝ) 1 ×ˢ Set.univ))
    (hG0 : ∀ A : traceSphere ν, G (0,A) = WithLp.toLp 2 (signedExtension f A.val))
    (hGz : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ A : traceSphere ν, G (t,A) ≠ 0)
    {y : Y} (hy : y ≠ 0) :
    ∃ A : traceSphere ν, ∃ t : ℝ, 0 < t ∧ G (1,A) = t • y := by
  classical
  let n := Fintype.card ι
  have hnz : n ≠ 0 := by dsimp [n]; omega
  let : NeZero n := ⟨hnz⟩
  let ea : UpperTriangle ν ≃ Fin n := (Fintype.equivFin _).trans (finCongr hc)
  let eaL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let ebL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let A : EuclideanSpace ℝ (Fin n) → M := fun x => symmetricCoordinates (eaL.symm x)
  have hAc : Continuous A := symmetricCoordinates.continuous_of_finiteDimensional.comp eaL.symm.continuous
  have hAs (x : EuclideanSpace ℝ (Fin n)) : IsSelfAdjoint (A x) := symmetricCoordinates_selfAdjoint _
  have hAz (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ annulus n) : A x ≠ 0 := by
    intro hz
    have h0 : eaL.symm x = 0 := symmetricCoordinates_injective (hz.trans (map_zero _).symm)
    have hx0 : x = 0 := eaL.symm.injective (h0.trans (map_zero _).symm)
    have hd := hx.1
    rw [hx0,norm_zero] at hd
    norm_num at hd
    exact hnz hd
  let N : annulus n → traceSphere ν := fun x =>
    ⟨traceRadial (A x.val),traceRadial_mem (hAs _) (hAz _ x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact traceRadial_continuousOn.comp_continuous (hAc.comp continuous_subtype_val)
      (fun x => hAz _ x.property)
  let H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun p =>
    if hx : p.2 ∈ annulus n then ebL (G (p.1,N ⟨p.2,hx⟩)) else 0
  have hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let S := Set.Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : S => N ⟨p.val.2,p.property.2⟩) :=
      hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hG.comp_continuous (continuous_subtype_val.fst.prodMk hcN)
      (fun p : S => ⟨p.property.1,Set.mem_univ _⟩)
    apply (ebL.continuous.comp hg).congr
    intro p
    change ebL (G (p.val.1,N ⟨p.val.2,p.property.2⟩)) = H p.val
    simp only [H,dite_eq_left p.property.2]
  have hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0 := by
    intro p hp hz
    have he : G (p.1,N ⟨p.2,hp.2⟩) = 0 := ebL.injective (by simpa only [H,dite_eq_left hp.2,map_zero] using hz)
    exact hGz _ hp.1 _ he
  have hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x) := by
    intro x hx
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [H,dite_eq_left hx,dite_eq_left hxn,hG0,N]
    have hAn : A (-x) = -A x := by simp only [A,map_neg]
    rw [hAn,traceRadial_neg,signedExtension_odd,WithLp.toLp_neg,map_neg]
  have hY : ‖ebL (unitRadial y)‖ = 1 := by rw [ebL.norm_map,unitRadial_norm hy]
  obtain ⟨x,hx,he⟩ := odd_homotopy_surjective n hn H hH hHz hHo hY
  let z : Y := G (1,N ⟨x,hx⟩)
  have hz : z ≠ 0 := hGz _ ⟨zero_le_one,le_rfl⟩ _
  have he' : unitRadial z = unitRadial y := by
    apply ebL.injective
    have heL : ebL (unitRadial z) = unitRadial (ebL z) := by simp only [unitRadial,map_smul,ebL.norm_map]
    rw [heL]
    simpa only [H,dite_eq_left hx] using he
  refine ⟨N ⟨x,hx⟩,‖z‖ / ‖y‖,div_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hy),?_⟩
  have hh := congrArg (fun v : Y => ‖z‖ • v) he'
  simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul,
    ← div_eq_mul_inv] using hh

end TraceHomotopy
end BorsukNine

end OAI
