import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorWordEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureMap

namespace OAI

/-! # Exact finite blocks of countable future labels -/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationSigma_le_of_fiber_refinement {Y α β : Type*}
    (P : Y → α) (Q : Y → β)
    (href : ∀ x y, Q x=Q y → P x=P y) :
    observationSigma P ≤ observationSigma Q := by
  rintro s ⟨t,_,rfl⟩
  refine ⟨Q '' (P ⁻¹' t),trivial,?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,hyx⟩
    change P x ∈ t
    rw [←href y x hyx]
    exact hy
  · intro hx
    exact ⟨x,hx,rfl⟩

def futureLabelBlock {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (N : ℕ) (x : Y) : ℕ :=
  Encodable.encode (fun i : Fin N => Q (T^[i.val+1] x))

lemma futureLabelBlock_measurable {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q) (N : ℕ) :
    Measurable (futureLabelBlock T Q N) := by
  exact (measurable_of_countable (Encodable.encode : (Fin N → ℕ) → ℕ)).comp
    (measurable_pi_iff.mpr fun i => hQ.comp (hT.iterate (i.val+1)))

lemma futureLabelBlock_eq_iff {Y : Type*} (T : Y → Y) (Q : Y → ℕ)
    (N : ℕ) (x y : Y) :
    futureLabelBlock T Q N x=futureLabelBlock T Q N y ↔
      ∀ i : Fin N, Q (T^[i.val+1] x)=Q (T^[i.val+1] y) := by
  exact Encodable.encode_injective.eq_iff.trans funext_iff

lemma futureLabelBlock_sigma_monotone {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    Monotone (fun N => observationSigma (futureLabelBlock T Q N)) := by
  intro N M hNM
  apply observationSigma_le_of_fiber_refinement
  intro x y hxy
  rw [futureLabelBlock_eq_iff] at hxy ⊢
  intro i
  exact hxy ⟨i.val,lt_of_lt_of_le i.isLt hNM⟩

lemma futureLabelBlock_sigma_generate {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    (⨆ N, observationSigma (futureLabelBlock T Q N)) =
      ⨆ k : ℕ, observationSigma (fun x => Q (T^[k+1] x)) := by
  apply le_antisymm
  · let : MeasurableSpace Y := ⨆ k : ℕ, observationSigma (fun x => Q (T^[k+1] x))
    apply iSup_le
    intro N
    have hQ (k : ℕ) : Measurable (fun x => Q (T^[k+1] x)) :=
      (comap_measurable _).iSup' k
    have hm : Measurable (futureLabelBlock T Q N) :=
      (measurable_of_countable (Encodable.encode : (Fin N → ℕ) → ℕ)).comp
        (measurable_pi_iff.mpr fun i => hQ i.val)
    exact hm.comap_le
  · apply iSup_le
    intro k
    apply le_trans _ (le_iSup (fun N => observationSigma (futureLabelBlock T Q N)) (k+1))
    apply observationSigma_le_of_fiber_refinement
    intro x y hxy
    exact (futureLabelBlock_eq_iff T Q (k+1) x y).mp hxy ⟨k,Nat.lt_succ_self k⟩

lemma futureLabelBlock_eq_iff_predecessor_symbols {Y : Type*} {M : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (B : Y → Fin M)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) (x y : Y) :
    futureLabelBlock T Q (N+1) x=futureLabelBlock T Q (N+1) y ↔
      Q (T^[N+1] x)=Q (T^[N+1] y) ∧
        futureName T B N x=futureName T B N y := by
  rw [futureLabelBlock_eq_iff]
  constructor
  · intro h
    refine ⟨h ⟨N,Nat.lt_succ_self N⟩,?_⟩
    funext i
    change B (T^[i.val] (T x))=B (T^[i.val] (T y))
    apply href
    · simpa only [←Function.iterate_succ_apply] using h ⟨i.val,Nat.lt_succ_of_lt i.isLt⟩
    · simpa only [←Function.iterate_succ_apply,←Function.iterate_succ_apply'] using
        h ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩
  · rintro ⟨ht,hb⟩
    have ht' : Q (T^[N] (T x))=Q (T^[N] (T y)) := by
      simpa only [←Function.iterate_succ_apply] using ht
    have hh := predecessor_word_recovers T Q B decode hdecode ht'
      (fun k hk => congrFun hb ⟨k,hk⟩)
    intro i
    simpa only [←Function.iterate_succ_apply] using hh i.val (by omega)

end DukePrimeDegree

end

end OAI
