import OAI.Computability.PerfectCompleteness.Machines.BinaryDualCoordinates

namespace OAI

section

namespace PerfectCompleteness.AffineLinearHeavyWitness

open scoped BigOperators
open QuarterBalance (F2)
open BinaryDualCoordinates
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {U V K I J : Type*}
  [AddCommGroup U] [Module F2 U] [Fintype U]
  [AddCommGroup V] [Module F2 V]
  [AddCommGroup K] [Module F2 K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def conditionalMatch (μ : FiniteDistribution U) (R : U →ₗ[F2] V) (target : V)
    (G : U → K) (T : U →ₗ[F2] K) (offset : K) : ℝ := by
  classical
  exact μ.expectation (fun x => if R x = target then
    (if G x = offset + T x then 1 else 0) else 0) /
  μ.expectation (fun x => if R x = target then 1 else 0)

omit [DecidableEq I] [DecidableEq J] in
theorem conditionalEquality_coordinates (μ : FiniteDistribution U)
    (b : Module.Basis I F2 V) (c : Module.Basis J F2 K)
    (R : U →ₗ[F2] V) (target : V) (G : U → K)
    (T : U →ₗ[F2] K) (offset : K) :
    OutputCharacters.conditionalEquality μ (equations b R) (coordinates b target)
      (fun x => coordinates c (G x)) (fun x => coordinates c (offset + T x)) =
      conditionalMatch μ R target G T offset := by
  classical
  simp only [OutputCharacters.conditionalEquality, OutputCharacters.sliceCorrelation,
    SmallBiasSlice.sliceNumerator, SmallBiasSlice.sliceMass, conditionalMatch,
    equations_eq_iff, (coordinates_injective c).eq_iff]

def badMasks (c : Module.Basis J F2 K) (bad : Finset (Module.Dual F2 K)) :
    Finset (J → Bool) :=
  bad.map (frequencyEquiv c).symm.toEmbedding

omit [DecidableEq J] in
@[simp] theorem mem_badMasks (c : Module.Basis J F2 K)
    (bad : Finset (Module.Dual F2 K)) (s : J → Bool) :
    s ∈ badMasks c bad ↔ frequency c s ∈ bad := by
  classical
  constructor
  · rintro h
    obtain ⟨f, hf, heq⟩ := Finset.mem_map.mp h
    have heq' : frequency c s = f := by
      change (frequencyEquiv c) s = f
      rw [← heq]
      exact (frequencyEquiv c).apply_symm_apply f
    simpa only [heq'] using hf
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨frequency c s, h, ?_⟩
    exact (frequencyEquiv c).symm_apply_apply s

omit [DecidableEq J] in
@[simp] theorem card_badMasks (c : Module.Basis J F2 K)
    (bad : Finset (Module.Dual F2 K)) :
    (badMasks c bad).card = bad.card := Finset.card_map _

theorem exists_heavy_in_dual_coset [Fintype (Module.Dual F2 U)]
    [Fintype (Module.Dual F2 K)]
    (μ : FiniteDistribution U)
    (b : Module.Basis I F2 V) (c : Module.Basis J F2 K)
    (R : U →ₗ[F2] V) (hR : Function.Surjective R) (target : V)
    (G : U → K) (T : U →ₗ[F2] K) (offset : K)
    (bad : Finset (Module.Dual F2 K)) (rho h0 biasBound : ℝ)
    (hrho : 0 < rho) (hh0 : 0 < h0)
    (hsize : h0 ≤ 1 / (Fintype.card (I → Bool) : ℝ))
    (hb : 0 ≤ biasBound) (hbsmall : biasBound ≤ h0 / 2)
    (hbias : ∀ f : Module.Dual F2 U, f ≠ 0 →
      |μ.expectation (character f)| ≤ biasBound)
    (hbad : (bad.card : ℝ) / (Fintype.card (Module.Dual F2 K) : ℝ) < rho / 8)
    (hmatch : rho ≤ conditionalMatch μ R target G T offset) :
    ∃ σ : Module.Dual F2 K, σ ∉ bad ∧
      ∃ ψ ∈ LinearMap.range R.dualMap,
        σ.comp T + ψ ∈ SmallBias.heavySet μ character
          (fun x => character σ (G x)) (rho * h0 / 4) := by
  classical
  have hcard : Fintype.card (J → Bool) = Fintype.card (Module.Dual F2 K) :=
    Fintype.card_congr (frequencyEquiv c)
  have hbad' : ((badMasks c bad).card : ℝ) /
      (Fintype.card (J → Bool) : ℝ) < rho / 8 := by
    simpa only [card_badMasks, hcard] using hbad
  have hmatch' : rho ≤ OutputCharacters.conditionalEquality μ (equations b R)
      (coordinates b target) (fun x => coordinates c (G x))
      (fun x => coordinates c (offset + T x)) := by
    rwa [conditionalEquality_coordinates]
  obtain ⟨s, hs, mask, hmask⟩ :=
    OutputCharacters.equality_implies_affine_heavy_witness μ
      character character_zero character_add (equationRows b R) (equations b R)
      (character_equationRows b R) (equationRows_independent b R hR)
      (coordinates b target) (fun x => coordinates c (G x))
      (fun x => coordinates c (offset + T x))
      (fun s => (frequency c s).comp T) (fun s => character (frequency c s) offset)
      (fun s => abs_character _ _) (character_affine_target c T offset)
      (badMasks c bad) rho h0 biasBound hrho hh0 hsize hb hbsmall hbias hbad' hmatch'
  refine ⟨frequency c s, (mem_badMasks c bad s).not.mp hs,
    SmallBiasSlice.rowCombination (equationRows b R) mask,
    rowCombination_mem_dualRange b R mask, ?_⟩
  simpa only [← character_frequency] using hmask

end
end PerfectCompleteness.AffineLinearHeavyWitness

end

end OAI
