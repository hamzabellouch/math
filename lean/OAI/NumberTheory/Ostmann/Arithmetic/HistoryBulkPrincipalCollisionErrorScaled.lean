import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction CanonicalOccurrenceTransport Conclusion Filter CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryCompensationBiasedKernelSum
open HistorySelectedPairDerivativeBounds
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_collisionPrincipalMean_scaled_error_eventually
    (d : Decomposition) (Bs BD Bz D : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)  ≤  C.blockBase  → 
      C.blockBase+favorableBlockWidth L  ≤  Real.exp ((9/10:ℝ)*L)  → 
      C.blockBase-2 < (C.giantCenter:ℝ)  → 
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2  → 
      |(C.bulkBin:ℝ)|  ≤  favorableBlockWidth L/16  → 
      |(C.spectatorBin:ℝ)|  ≤  favorableBlockWidth L/16  → 
      ∀ (spectator : PrimeSource),
      (∀ p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)  ≤  Real.log (p:ℕ) ∧
        Real.log (p:ℕ)  ≤  Real.exp ((1/1000:ℝ)*L))  → 
      ∀ (l : ℕ) (corrected mixed : Bool), (if corrected then l<k else l ≤ k)  → 
      ∀ (outside : List ℕ), outside.length  ≤  bulkSize k L  → 
      (∀q∈outside,∃p:spectator.Sample,p.val=q ∧ spectator.law.mass p≠0)  → 
      ∀ (a : SelectedNonbulkSample C l), (selectedNonbulkPrior C l).mass a≠0  → 
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let origin := pairedInternalOrigin seed l
      let τ := pairedHistoryType seed l
      ∀ (refs : ∀p:Pattern τ,(Block p → CommonSample C.sources origin)  → 
          Option (PrincipalCollisionReference C outside a p))
        (mask : SelectedBulkSample C l  →  ∀p:Pattern τ,
          (Block p → CommonSample C.sources origin)  →  ℝ),
      (∀u p b,0  ≤  mask u p b ∧ mask u p b  ≤  1)  → 
      ‖collisionPrincipalMean C origin τ outside a refs mask corrected mixed true-
        collisionPrincipalMean C origin τ outside a refs mask corrected mixed false‖ * Real.exp (D*(L+1)^2) ≤ 
          Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  filter_upwards [selected_symbolic_guard_error_eventually d Bs BD Bz
      (selectedExponent Bs BD Bz k+64) D hk,
    selected_principalAmplitudeData_norm_eventually d Bs BD Bz hBs (by omega : 0<k)] with
    L herror hamp
  intro E C hG hGu hcl hcu hb hd spectator hs l corrected mixed hl outside hlen hout a ha
  dsimp only
  intro refs mask hm
  let seed := Template.initial (2*(bulkSize k L/2)) k
  let origin := pairedInternalOrigin seed l
  let τ := pairedHistoryType seed l
  let μ := selectedBulkPrior C l
  let mask' := fun (u:SelectedBulkSample C l) (p:Pattern τ)
    (b:Block p → CommonSample C.sources origin) => if (refs p b).isSome then mask u p b else 0
  let rs := collisionPatternReferences C origin τ outside a refs
  let amp := collisionAmplitude C origin τ outside a refs corrected mixed
  let c : ℂ := Real.exp (D*(L+1)^2)
  let scaled := fun u p b => c*amp u p b
  let K := fun _ : SelectedBulkSample C l => optionalDrawSymbolicPatternKernel C.sources origin τ
    mixed (frequencyBound Bs BD Bz k L) outside l rs
  have hc : ‖c‖ = Real.exp (D*(L+1)^2) := by
    simp only [c,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hl' : l ≤ k := by cases corrected <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hl <;> omega
  have hm' : ∀u p b,0 ≤ mask' u p b ∧ mask' u p b ≤ 1 := by
    intro u p b
    dsimp only [mask']
    split_ifs
    · exact hm u p b
    · norm_num
  have hr : ∀u,μ.mass u≠0  →  ∀(p:Pattern τ) (b:BlockDraw p (CommonSample C.sources origin)),
      mask' u p b.val≠0  →  ∃y,fibreSmallOutsideGuard C outside a y := by
    intro u hu p b hb
    cases hh : refs p b.val with
    | none => simp only [mask',hh,Option.isSome_none,Bool.false_eq_true,ite_false,ne_eq,not_true_eq_false] at hb
    | some r => exact ⟨r.referenceBulk,r.reference_guard⟩
  have ha' : ∀u,μ.mass u≠0 → ∀p b,mask' u p b.val≠0 →
      ‖scaled u p b‖ ≤ ((outside.prod:ℝ)^(2^(l+1))*
        Real.exp ((selectedExponent Bs BD Bz k+64)*((bulkSize k L:ℝ)+1)))*Real.exp (D*(L+1)^2) := by
    intro u hu p b hb
    have ha0 : ‖amp u p b‖ ≤ (outside.prod:ℝ)^(2^(l+1))*
        Real.exp ((selectedExponent Bs BD Bz k+64)*((bulkSize k L:ℝ)+1)) := by
      cases hh : refs p b.val with
      | none => simp only [amp,collisionAmplitude,hh,norm_zero]; positivity
      | some r =>
        simpa only [amp,collisionAmplitude,hh,PrincipalCollisionReference.value] using
          hamp E C hG hcl outside l (r.amplitudeAt u) corrected mixed hl u
    dsimp only [scaled]
    rw [norm_mul,hc,mul_comm]
    exact mul_le_mul_of_nonneg_right ha0 (Real.exp_nonneg _)
  have he := herror E C hG hGu hcl hcu hb hd spectator hs l hl' outside hlen hout a ha
    mixed (frequencyBound Bs BD Bz k L) (fun _=>rs) mask' scaled hm' hr ha'
  change ‖originalBulkPrincipalSum C.sources origin τ μ mask'
      (fun u p b => if fibreSmallOutsideGuard C outside a u then
        principalTest C.sources origin τ K scaled u p b else 0)-
    originalBulkPrincipalSum C.sources origin τ μ mask'
      (principalTest C.sources origin τ K scaled)‖ ≤ _ at he
  have hleft : originalBulkPrincipalSum C.sources origin τ μ mask'
      (fun u p b => if fibreSmallOutsideGuard C outside a u then
        principalTest C.sources origin τ K scaled u p b else 0) =
      c*collisionPrincipalMean C origin τ outside a refs mask' corrected mixed true := by
    rw [←collisionPrincipalMean_scaledTest C origin τ outside a refs mask' corrected mixed true c]
    apply congrArg (originalBulkPrincipalSum C.sources origin τ μ mask')
    funext u p b
    by_cases hg : fibreSmallOutsideGuard C outside a u <;> simp only [hg,not_true_eq_false,
      not_false_eq_true,and_false,and_true,ite_true,ite_false]
    rfl
  have hright : originalBulkPrincipalSum C.sources origin τ μ mask'
      (principalTest C.sources origin τ K scaled) =
      c*collisionPrincipalMean C origin τ outside a refs mask' corrected mixed false := by
    rw [←collisionPrincipalMean_scaledTest C origin τ outside a refs mask' corrected mixed false c]
    simp only [Bool.false_eq_true,false_and,ite_false]
    rfl
  rw [hleft,hright,←mul_sub,norm_mul,hc,mul_comm] at he
  rw [collisionPrincipalMean_activeMask C origin τ outside a refs mask corrected mixed true,
    collisionPrincipalMean_activeMask C origin τ outside a refs mask corrected mixed false]
  exact he

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
