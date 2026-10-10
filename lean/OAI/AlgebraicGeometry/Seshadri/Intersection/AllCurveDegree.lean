import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.AmpleCurveDegree

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames MaximalSeshadri.SectionOpens
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
variable {σ : Type} [Fintype σ]
variable (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
include hd a ha

theorem projective_curve_positive_bundle :
    ∃ (H : LineBundle X) (s : O X ⟶ H.sheaf) (x : X),
      x ∈ isoOpen s ∧ 0 < eulerCharacteristic p 1 H.sheaf - eulerCharacteristic p 1 (O X) := by
  let H : LineBundle X := ⟨A,fun x => by
    have hx : x ∈ ⨆ i, isoOpen (a i) := ha ▸ trivial
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨isoOpen (a i),hi,⟨sectionFrame (a i)⟩⟩⟩
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, isoOpen (a i) := ha ▸ trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  have hne : a i ≠ 0 := section_ne_zero_of_mem_isoOpen H (a i) x hi
  refine ⟨H,a i,x,hi,projective_section_positive_degree p hd a ha H (a i) hne ?_⟩
  intro he
  have hA := (Proj.isAffineOpen_basicOpen (PolyGrade ℂ σ) _ (poly_X_mem i)
    (by decide)).preimage (sectionsMorphism (baseScalars p) a ha)
  rw [sectionsMorphism_preimage,he] at hA
  let : IsAffine (⊤ : X.Opens).toScheme := hA
  let : IsAffine X := .of_isIso X.topIso.inv
  have hdim := proper_affine_dimension_zero p
  rw [hd] at hdim
  norm_num at hdim

theorem projective_curve_tensor_euler_add (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  obtain ⟨H,s,x,hx,hpos⟩ := projective_curve_positive_bundle p hd a ha
  have hs := section_ne_zero_of_mem_isoOpen H s x hx
  obtain ⟨k,hk⟩ := exists_nat_gt (-eulerCharacteristic p 1 L.sheaf)
  let t : O X ⟶ (H.pow k).sheaf := powerSection s k
  have ht : t ≠ 0 := section_ne_zero_of_mem_isoOpen (H.pow k) t x
    (sectionOpen_le_powerSection s k hx)
  have he₀ := projective_section_tensor_euler_add p hd a ha (H.pow k) L t ht
  have hepow := projective_section_power_euler p hd a ha H s hs k
  have hpositive : 0 < eulerCharacteristic p 1 ((H.pow k).tensor L).sheaf := by
    have hk' : (0 : ℤ) ≤ k := Nat.cast_nonneg k
    have hh : 1 ≤ eulerCharacteristic p 1 H.sheaf - eulerCharacteristic p 1 (O X) := hpos
    nlinarith
  obtain ⟨u,hu⟩ := positive_curve_euler_section p ((H.pow k).tensor L).sheaf hpositive
  have he₁ := projective_section_tensor_euler_add p hd a ha ((H.pow k).tensor L) M u hu
  have he₂ := projective_section_tensor_euler_add p hd a ha (H.pow k) (L.tensor M) t ht
  have e := eulerCharacteristic_iso p (lineTensorAssoc (H.pow k) L M) 1
  change eulerCharacteristic p 1 (((H.pow k).tensor L).tensor M).sheaf =
    eulerCharacteristic p 1 ((H.pow k).tensor (L.tensor M)).sheaf at e
  linarith

theorem projective_curve_power_euler (L : LineBundle X) (n : ℕ) :
    eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (O X) =
      (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X)) := by
  induction n with
  | zero => simp [LineBundle.pow,modulePow,O]
  | succ n ih =>
    have he := projective_curve_tensor_euler_add p hd a ha L (L.pow n)
    change eulerCharacteristic p 1 (L.pow (n+1)).sheaf -
      eulerCharacteristic p 1 (L.pow n).sheaf = _ at he
    push_cast
    nlinarith

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
