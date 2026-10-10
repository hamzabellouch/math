import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorGuard
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionAtoms
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPrincipalBudgetDrawReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum HistoryCompensationPrincipalBudget
open HistoryBulkSourceDisintegration HistoryBulkSourceCollision HistoryBulkSourceCollisionBirthday
open Conclusion Filter
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_symbolic_guard_error_eventually
    (d : Decomposition) (Bs BD Bz A D : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ (spectator : PrimeSource),
      (∀ p : spectator.Sample,Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ (l : ℕ), l ≤ k →
      ∀ (outside : List ℕ), outside.length ≤ bulkSize k L →
      (∀q∈outside,∃p:spectator.Sample,p.val=q ∧ spectator.law.mass p≠0) →
      ∀ (a : SelectedNonbulkSample C l), (selectedNonbulkPrior C l).mass a≠0 →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let origin := pairedInternalOrigin seed l
      let τ := pairedHistoryType seed l
      ∀ (mixed : Bool) (V : ℕ→ℕ)
        (refs : SelectedBulkSample C l → ∀p:Pattern τ,
          (Block p → CommonSample C.sources origin) → Option (PatternReference p V outside l))
        (mask : SelectedBulkSample C l → ∀p:Pattern τ,
          (Block p → CommonSample C.sources origin) → ℝ)
        (amp : SelectedBulkSample C l → ∀p:Pattern τ,
          BlockDraw p (CommonSample C.sources origin) → ℂ),
      (∀u p b,0 ≤ mask u p b ∧ mask u p b ≤ 1) →
      (∀u,(selectedBulkPrior C l).mass u≠0 → ∀(p : Pattern τ) (b : BlockDraw p (CommonSample C.sources origin)),mask u p b.val≠0 →
        ∃y,fibreSmallOutsideGuard C outside a y) →
      (∀u,(selectedBulkPrior C l).mass u≠0 → ∀p b,mask u p b.val≠0 →
        ‖amp u p b‖≤((outside.prod:ℝ)^(2^(l+1))*Real.exp (A*((bulkSize k L:ℝ)+1)))*
          Real.exp (D*(L+1)^2)) →
      let K := fun u => optionalDrawSymbolicPatternKernel C.sources origin τ mixed V outside l (refs u)
      ‖originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask
          (fun u p b => if fibreSmallOutsideGuard C outside a u then
            principalTest C.sources origin τ K amp u p b else 0)-
        originalBulkPrincipalSum C.sources origin τ (selectedBulkPrior C l) mask
          (principalTest C.sources origin τ K amp)‖≤Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  filter_upwards [selected_fibreSmallOutsideGuard_eventually d Bs BD Bz (by omega : 0<k),
    selected_optionalDrawSymbolicKernelSum_eventually d Bs BD Bz hk,
    bulk_atom_bound_eventually,selected_compensated_collision_budget_eventually k A D] with
    L hguard hkernel hatom hcost
  intro E C hG hGu hcl hcu hb hd spectator hs l hl outside hlen hout a ha
  dsimp only
  intro mixed V refs mask amp hm href hamp
  let seed := Template.initial (2*(bulkSize k L/2)) k
  let origin := pairedInternalOrigin seed l
  let τ := pairedHistoryType seed l
  let μ := selectedBulkPrior C l
  let K := fun u => optionalDrawSymbolicPatternKernel C.sources origin τ mixed V outside l (refs u)
  let W := ((outside.prod:ℝ)^(2^(l+1))*Real.exp (A*((bulkSize k L:ℝ)+1)))*Real.exp (D*(L+1)^2)
  let M := Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ))
  have hW : 0≤W := by dsimp [W]; positivity
  have hM : 0≤M := Real.exp_nonneg _
  have hK : ∀u p b q,0≤K u p b q :=
    fun u p b q => (optionalDrawSymbolicPatternKernel_bounds C.sources origin τ mixed V outside l (refs u) p b q).1
  have he := originalBulkPrincipalSum_guard_error_le C.sources origin τ μ
    (fun u => ¬Function.Injective (fun i => (u i).val)) K mask
    (fun u _ _ => fibreSmallOutsideGuard C outside a u) amp W M hW hM hK
    (fun u p b => (hm u p b).1)
    (fun u _ => hkernel E C hG hGu hcl hcu hb hd l hl mixed V outside (refs u) (mask u) (hm u))
    (by
      intro u hu hgood p b hactive
      obtain ⟨y,hy⟩ := href u hu p b hactive
      exact hguard E C hG hcl hcu hb hd spectator hs l a u y ha hu outside hout hy (not_not.mp hgood))
    hamp
  have hbday := primeSource_noninjective_mass_le
    (ι:=Fin (2^l) × Fin (2*(bulkSize k L/2))) C.bulk _
    (hatom E C.deleted_card C.bulkPositive)
  have hpos : ∀p∈outside,0<p := by
    intro p hp
    obtain ⟨q,rfl,hq⟩ := hout p hp
    exact (spectator.prime q.val q.property).pos
  have hlog : ∀p∈outside,Real.log (p:ℝ)≤Real.exp ((1/1000:ℝ)*L) := by
    intro p hp
    obtain ⟨q,rfl,hq⟩ := hout p hp
    exact (hs q).2
  have hbday' : μ.mean (fun u => if ¬Function.Injective (fun i => (u i).val) then 1 else 0) ≤
      ((2^l*(2*(bulkSize k L/2)):ℕ):ℝ)^2*Real.exp (L-Real.exp ((39/10000:ℝ)*L)) := by
    simpa only [μ,selectedBulkPrior,bulkPrior,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using hbday
  apply he.trans
  calc
    _ ≤ W*M*(((2^l*(2*(bulkSize k L/2)):ℕ):ℝ)^2*
        Real.exp (L-Real.exp ((39/10000:ℝ)*L))) := by
      convert mul_le_mul_of_nonneg_left hbday' (mul_nonneg hW hM) using 1
      congr 1
      apply congrArg μ.mean
      funext u
      by_cases hh : Function.Injective (fun i => (u i).val) <;>
        simp only [hh,not_true_eq_false,not_false_eq_true,ite_true,ite_false]
    _ ≤ _ := by
      have hc := hcost l hl outside hpos hlen hlog
      dsimp only [W,M]
      convert hc using 1
      ring

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
