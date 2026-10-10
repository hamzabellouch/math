import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuliBoundsBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceNewModuli
open Construction Conclusion Filter HistoryCRTIntegration HistorySignedResidues HistoryPairBulkTransport
open HistoryGiantIndependentModulus HistoryGiantReferenceMean HistorySignedXiTransport

theorem selected_newComparisonModulus_cap_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase → C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      let outside := spectatorList spectator ds
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      let T := Template.current seed l
      ∀ (x x₀ y₀ : SourceAssignment C.sources T) (snew s t : ℤ) (gp gm : ℕ) (P Q : ℤ)
        (cnew c e : HistoryChoices C.sources seed V l),
      (assignmentPrior C.sources T).mass x ≠ 0 →
      (assignmentPrior C.sources T).mass x₀ ≠ 0 →
      (assignmentPrior C.sources T).mass y₀ ≠ 0 →
      choicesMass C.sources seed V l c ≠ 0 → choicesMass C.sources seed V l e ≠ 0 →
      let newh := assignedHistory C.sources seed V l snew gp gm x cnew
      let oldh := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x₀ s) P Q) c
      let oldk := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y₀ t) P Q) e
      oldh.Supported V outside → oldk.Supported V outside →
      0 < newComparisonModulus newh oldh oldk outside k ∧
        Real.log (newComparisonModulus newh oldh oldk outside k:ℝ) ≤ Real.exp ((3/250:ℝ)*L) ∧
        (newComparisonModulus newh oldh oldk outside k:ℝ) ≤ Real.exp (Real.exp ((3/250:ℝ)*L)) := by
  filter_upwards [selected_assigned_rootModulus_le_eventually d Bs BD Bz hk,
    selected_fixedSmall_factorBound_eventually d Bs BD Bz hk,
    actual_newComparisonModulus_log_le_eventually Bs BD Bz k,
    eventually_ge_atTop (0:ℝ)] with L hroot hbound hlog hL
  intro E C hG hcl hcu hb hd spectator hspec ds
  dsimp only
  intro l hl x x₀ y₀ snew s t gp gm P Q cnew c e hx hx₀ hy₀ hc he hs gs
  have hr := hroot E C hG hcl hcu hb hd l hl x snew gp gm cnew hx
  have hh := hbound E C hG hcl hcu hb hd l hl
    (giantState (sourceState C.sources _ x₀ s) P Q) c (spectatorList spectator ds)
    (Template.assignedSlots_matches _ _ _) (assignedSlots_source_mass_ne_zero _ _ _ hx₀) hc hs
  have hg := hbound E C hG hcl hcu hb hd l hl
    (giantState (sourceState C.sources _ y₀ t) P Q) e (spectatorList spectator ds)
    (Template.assignedSlots_matches _ _ _) (assignedSlots_source_mass_ne_zero _ _ _ hy₀) he gs
  have hprime : ∀ q∈spectatorList spectator ds,q.Prime := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact spectator.prime (ds i).val (ds i).property
  have hpos : 0 < newComparisonModulus
      (assignedHistory C.sources _ _ l snew gp gm x cnew)
      (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ x₀ s) P Q) c)
      (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ y₀ t) P Q) e)
      (spectatorList spectator ds) k :=
    mul_pos (mul_pos (mul_pos (assigned_rootModulus_pos C.sources _ _ l snew gp gm x cnew)
      (outsideModulus_pos hprime)) (frequencyModulus_pos _ _ hs gs (k+2)))
      (representativeModulus_pos _ _ hs gs)
  have hout : ∀ q∈spectatorList spectator ds,(q:ℝ) ≤ actualFactorCap Bs BD Bz k L := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact spectator_le_actualFactorCap Bs BD Bz k hL
      (spectator.prime (ds i).val (ds i).property).pos (hspec (ds i))
  have hcap := hlog l hl _ _ _ (spectatorList spectator ds) hr hh hg
    (initial_spectator_count_le k L spectator ds) hout hpos
  refine ⟨hpos,hcap,?_⟩
  have hp : (0:ℝ) < newComparisonModulus
      (assignedHistory C.sources _ _ l snew gp gm x cnew)
      (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ x₀ s) P Q) c)
      (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ y₀ t) P Q) e)
      (spectatorList spectator ds) k := by exact_mod_cast hpos
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hcap

end Ostmann.Arithmetic.HistoryBulkReferenceNewModuli

end

end OAI
