import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CohomologyIso
import OAI.AlgebraicGeometry.Seshadri.Intersection.CurveDegreeAdditivity

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma positive_curve_euler_section (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules)
    (hpos : 0 < eulerCharacteristic p 1 M) : ∃ s : O X ⟶ M, s ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  let : Subsingleton Γ(M,⊤) := ⟨fun x y =>
    (moduleSectionEquiv M).symm.injective ((hn _).trans (hn _).symm)⟩
  have hz : cohomologyDimension p M 0 = 0 := by
    rw [cohomologyDimension_zero]
    let := Module.compHom Γ(M,⊤) (baseScalars p)
    exact Module.finrank_zero_of_subsingleton
  rw [eulerCharacteristic,Finset.sum_range_succ,Finset.sum_range_succ] at hpos
  simp only [Finset.sum_range_zero,zero_add,pow_zero,one_mul,hz,Nat.cast_zero,
    pow_one,neg_mul,one_mul,zero_add] at hpos
  omega

variable [IsIntegral X] [IsNoetherian X]
variable {σ : Type} [Fintype σ]
variable (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]

include hd a ha

theorem projective_power_euler_progression (L : LineBundle X) (m : ℕ)
    (s : O X ⟶ (L.pow m).sheaf) (hs : s ≠ 0) (k n : ℕ) :
    eulerCharacteristic p 1 (L.pow (m*k+n)).sheaf =
      (k : ℤ) * (eulerCharacteristic p 1 (L.pow m).sheaf - eulerCharacteristic p 1 (O X)) +
        eulerCharacteristic p 1 (L.pow n).sheaf := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := projective_section_tensor_euler_add p hd a ha (L.pow m) (L.pow (m*k+n)) s hs
    change eulerCharacteristic p 1 (moduleTensor X (modulePow X L.sheaf m)
      (modulePow X L.sheaf (m*k+n))) - _ = _ at he
    rw [← eulerCharacteristic_iso p (linePowerAdd L m (m*k+n)) 1] at he
    change eulerCharacteristic p 1 (L.pow (m+(m*k+n))).sheaf - _ = _ at he
    have hi : m*(k+1)+n = m+(m*k+n) := by ring
    rw [hi]
    push_cast
    linarith

theorem projective_power_euler_of_positive_effective_power
    (L : LineBundle X) (m : ℕ) (s : O X ⟶ (L.pow m).sheaf) (hs : s ≠ 0)
    (hdeg : 0 < eulerCharacteristic p 1 (L.pow m).sheaf - eulerCharacteristic p 1 (O X))
    (n : ℕ) :
    eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (O X) =
      (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X)) := by
  let χ (j : ℕ) := eulerCharacteristic p 1 (L.pow j).sheaf
  let χ₀ := eulerCharacteristic p 1 (O X)
  have hprog (k j : ℕ) : χ (m*k+j) = (k : ℤ) * (χ m - χ₀) + χ j :=
    projective_power_euler_progression p hd a ha L m s hs k j
  obtain ⟨k,hk⟩ := exists_nat_gt (-χ 1)
  have hpos : 0 < χ (m*k+1) := by
    rw [hprog]
    have hm : 1 ≤ χ m - χ₀ := hdeg
    have hkn : (0 : ℤ) ≤ k := Nat.cast_nonneg k
    nlinarith
  obtain ⟨t,ht⟩ := positive_curve_euler_section p (L.pow (m*k+1)).sheaf hpos
  have hstep (j : ℕ) : χ (j+1) - χ j = χ 1 - χ₀ := by
    have he := projective_section_tensor_euler_add p hd a ha
      (L.pow (m*k+1)) (L.pow j) t ht
    change eulerCharacteristic p 1 (moduleTensor X (modulePow X L.sheaf (m*k+1))
      (modulePow X L.sheaf j)) - _ = _ at he
    rw [← eulerCharacteristic_iso p (linePowerAdd L (m*k+1) j) 1] at he
    change χ (m*k+1+j) - χ j = χ (m*k+1) - χ₀ at he
    have hj : m*k+1+j = m*k+(j+1) := by omega
    rw [hj,hprog,hprog] at he
    linarith
  have hresult (j : ℕ) : χ j - χ₀ = (j : ℤ) * (χ 1 - χ₀) := by
    induction j with
    | zero => simp [χ,χ₀,LineBundle.pow,modulePow,O]
    | succ j ih =>
      have hj := hstep j
      push_cast
      nlinarith
  have h1 : χ 1 = eulerCharacteristic p 1 L.sheaf := by
    exact eulerCharacteristic_iso p (moduleTensorRightUnit L.sheaf) 1
  change χ n - χ₀ = _
  rw [hresult,h1]

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
