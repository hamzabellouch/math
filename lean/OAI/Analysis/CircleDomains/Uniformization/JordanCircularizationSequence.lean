import OAI.Analysis.CircleDomains.Uniformization.JordanCircularizationStep
import OAI.Analysis.CircleDomains.Uniformization.PrincipalComposition

namespace OAI

/-! The actual sequence of finite Jordan configurations and normalized
conformal maps obtained by successive one-hole circularizations. -/
open Set Function Metric Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure FiniteJordanConfiguration (I : Type*) where
  hole : I → ℂ ≃ₜ ℂ
  disjoint : Pairwise (Disjoint on fun i => closure (jordanInterior (hole i)))

namespace FiniteJordanConfiguration
variable {I : Type*} [Finite I]

def region (C : FiniteJordanConfiguration I) : Set Sphere := openCompletedRegion C.hole

lemma region_open (C : FiniteJordanConfiguration I) : IsOpen C.region :=
  isOpen_openCompletedRegion C.hole

lemma region_connected (C : FiniteJordanConfiguration I) : IsConnected C.region :=
  isConnected_openCompletedRegion C.hole C.disjoint

omit [Finite I] in
lemma infty_mem_region (C : FiniteJordanConfiguration I) : ∞ ∈ C.region := by
  intro h
  obtain ⟨i,z,_hz,he⟩ := mem_iUnion.mp h
  exact OnePoint.coe_ne_infty z he

structure Step (C : FiniteJordanConfiguration I) (j : I) where
  target : FiniteJordanConfiguration I
  map : Sphere → Sphere
  center : ℂ
  radius : ℝ
  radius_pos : 0<radius
  principal : IsPrincipalNormalized map
  selected : jordanInterior (target.hole j)=ball center radius
  others : ∀ i, i≠j → map '' closedTerminalCap (C.hole i)=closedTerminalCap (target.hole i)
  conformal : IsConformalEquivalence map C.region target.region
  exterior_conformal : IsConformalEquivalence map (closedTerminalCap (C.hole j))ᶜ
    ((((↑) : ℂ → Sphere) '' closedBall center radius)ᶜ)

lemma step_nonempty (C : FiniteJordanConfiguration I) (j : I) : Nonempty (Step C j) := by
  obtain ⟨K,F,c,r,hr,hp,hd,hsel,ho,hext,hconf⟩ :=
    exists_jordan_circularization_step_full C.hole C.disjoint j
  exact ⟨⟨⟨K,hd⟩,F,c,r,hr,hp,hsel,ho,hconf,hext⟩⟩

def chosenStep (C : FiniteJordanConfiguration I) (j : I) : Step C j :=
  Classical.choice (step_nonempty C j)

def iterate (C : FiniteJordanConfiguration I) (schedule : ℕ → I) : ℕ → FiniteJordanConfiguration I
  | 0 => C
  | n+1 => (chosenStep (iterate C schedule n) (schedule n)).target

def stageMap (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) : Sphere → Sphere :=
  (chosenStep (iterate C schedule n) (schedule n)).map

def cumulativeMap (C : FiniteJordanConfiguration I) (schedule : ℕ → I) : ℕ → Sphere → Sphere
  | 0 => id
  | n+1 => stageMap C schedule n ∘ cumulativeMap C schedule n

lemma stageMap_principal (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    IsPrincipalNormalized (stageMap C schedule n) :=
  (chosenStep (iterate C schedule n) (schedule n)).principal

lemma stageMap_conformal (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    IsConformalEquivalence (stageMap C schedule n) (iterate C schedule n).region
      (iterate C schedule (n+1)).region :=
  (chosenStep (iterate C schedule n) (schedule n)).conformal

lemma cumulativeMap_principal (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    IsPrincipalNormalized (cumulativeMap C schedule n) := by
  induction n with
  | zero =>
    refine ⟨rfl,?_⟩
    simpa only [cumulativeMap,id_eq,finiteCoord_coe,sub_self] using
      (isBigO_zero (g := fun z : ℂ => z⁻¹) (l := cobounded ℂ))
  | succ n ih => exact (stageMap_principal C schedule n).comp ih

lemma cumulativeMap_conformal (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    IsConformalEquivalence (cumulativeMap C schedule n) C.region
      (iterate C schedule n).region := by
  induction n with
  | zero => exact isConformalEquivalence_id C.region
  | succ n ih => exact ih.trans (stageMap_conformal C schedule n)

lemma iterate_selected_round (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    ∃ c : ℂ, ∃ r : ℝ, 0<r ∧
      jordanInterior ((iterate C schedule (n+1)).hole (schedule n))=ball c r :=
  ⟨_,_,(chosenStep (iterate C schedule n) (schedule n)).radius_pos,
    (chosenStep (iterate C schedule n) (schedule n)).selected⟩

lemma stageMap_other_hole (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ)
    {i : I} (hi : i≠schedule n) :
    stageMap C schedule n '' closedTerminalCap ((iterate C schedule n).hole i)=
      closedTerminalCap ((iterate C schedule (n+1)).hole i) :=
  (chosenStep (iterate C schedule n) (schedule n)).others i hi

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
