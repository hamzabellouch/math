import Mathlib
import OAI.Combinatorics.UniformKServer.AdaptiveAlpha

namespace OAI

                                 
section

/-! Empty active domains are genuine zero states, not a hidden nonempty
 hypothesis. They occur only at wholesale changes in the derived schedule;
 the algebra here incurs no restart allowance. -/
noncomputable section
namespace UniformKServer.AlphaEmpty
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

abbrev Config (ι : Type*) := Option (AdaptiveAlpha.Config ι)

def active : Config ι → Finset ι
  | none => ∅
  | some p => p.active

def valid : Config ι → Prop
  | none => True
  | some p => AdaptiveAlpha.valid p

def state : Config ι → (ι → ℝ) → Prop
  | none, a => a=fun _ => 0
  | some p, a => DomainTransport.simplex p.active a

def potential : Config ι → (ι → ℝ) → (ι → ℝ) → ℝ
  | none, _, _ => 0
  | some p, B, a => AdaptiveAlpha.potential p B a

def scale : Config ι → ℝ
  | none => 0
  | some p => AdaptiveAlpha.scale p

def eta : Config ι → ι → ℝ
  | none, _ => 0
  | some p, i => AdaptiveAlpha.eta p i

omit [Fintype ι] in
theorem zero_supported {B : ι → ℝ} (hs : DomainTransport.Supported (∅ : Finset ι) B) :
    B=fun _ => 0 := by
  funext i
  exact hs i (by simp)

theorem exists_state {p : Config ι} (hp : valid p) : ∃ a, state p a := by
  cases p with
  | none => exact ⟨fun _ => 0,rfl⟩
  | some p => exact DomainTransport.exists_simplex hp.1

omit [Fintype ι] in
theorem scale_nonneg {p : Config ι} (hp : valid p) : 0 ≤ scale p := by
  cases p with
  | none => exact le_rfl
  | some p => exact AdaptiveAlpha.scale_nonneg hp

omit [Fintype ι] in
theorem potential_zero (p : Config ι) (a : ι → ℝ) : potential p (fun _ => 0) a=0 := by
  cases p with
  | none => rfl
  | some p => exact AdaptiveAlpha.potential_zero p a

theorem state_interval {p : Config ι} {a : ι → ℝ} (ha : state p a) (i : ι) :
    a i ∈ Set.Icc (0:ℝ) 1 := by
  cases p with
  | none => rw [ha]; simp
  | some p =>
    change DomainTransport.simplex p.active a at ha
    refine ⟨ha.1 i,?_⟩
    have h := single_le_sum (s:=univ) (f:=a) (fun j _ => ha.1 j) (mem_univ i)
    linarith [ha.2.2]

theorem input_bound {p : Config ι} (hp : valid p) (B B' a : ι → ℝ)
    (ha : state p a) :
    |potential p B a-potential p B' a| ≤ 15*scale p*(∑ i, |B i-B' i|) := by
  cases p with
  | none => simp [potential,scale]
  | some p => exact AdaptiveAlpha.input_bound hp B B' a ha

theorem update {p : Config ι} (hp : valid p) (B a₀ : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported (active p) B)
    (ha₀ : state p a₀) :
    ∃ a, state p a ∧ (∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) ∧
      (∑ j, B j)*SimplexTracker.movement a a₀ ≤ potential p B a₀-potential p B a := by
  cases p with
  | none =>
    have he := zero_supported hs
    refine ⟨fun _ => 0,rfl,?_,?_⟩
    · intro i; simp [eta,he]
    · simp [he,potential]
  | some p => exact AdaptiveAlpha.update hp B a₀ hB hs ha₀

/-- Two actual minimizing updates whenever both domains are nonempty.
 At an empty endpoint, actual zero input supplies the same ledger. -/
theorem step {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew a₀ : ι → ℝ) (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i)
    (hST : (∑ i, Bstar i) ≤ ∑ i, Bnew i)
    (hpB : DomainTransport.Supported (active p) Bstar)
    (hqB : DomainTransport.Supported (active q) Bstar)
    (hqN : DomainTransport.Supported (active q) Bnew)
    (ha₀ : state p a₀) :
    ∃ a b, state q a ∧ state q b ∧
      (∀ i, (∑ j, Bnew j)*a i ≤ (1+eta q i)*Bnew i) ∧
      (∀ i, (∑ j, Bstar j)*b i ≤ (1+eta p i)*Bstar i) ∧
      (∑ j, Bnew j)*SimplexTracker.movement a a₀ ≤
        potential p Bstar a₀-potential q Bnew a+
        (potential q Bstar b-potential p Bstar b)+
        15*scale q*(∑ i, |Bnew i-Bstar i|)+4*((∑ i, Bnew i)-(∑ i, Bstar i)) := by
  cases p with
  | none =>
    have hzero := zero_supported hpB
    have haold : a₀=fun _ => 0 := ha₀
    obtain ⟨b,hb⟩ := exists_state hq
    obtain ⟨a,ha,hf,_⟩ := update hq Bnew b hBn hqN hb
    refine ⟨a,b,ha,hb,hf,?_,?_⟩
    · intro i; simp [hzero]
    · have hi := input_bound hq Bnew (fun _ => 0) a ha
      rw [potential_zero,sub_zero] at hi
      have hsum : (∑ i, |Bnew i|)=∑ i, Bnew i := sum_congr rfl fun i _ => abs_of_nonneg (hBn i)
      simp only [sub_zero] at hi
      rw [hsum] at hi
      have hm : SimplexTracker.movement a a₀ ≤ 1 := by
        rw [haold]
        cases q with
        | none => rw [ha]; simp [SimplexTracker.movement]
        | some q =>
          change DomainTransport.simplex q.active a at ha
          simp only [SimplexTracker.movement,sub_zero,abs_of_nonneg (ha.1 _),ha.2.2]
          exact le_rfl
      have hT : 0 ≤ ∑ i, Bnew i := sum_nonneg fun i _ => hBn i
      have hmul := mul_le_mul_of_nonneg_left hm hT
      rw [hzero,potential_zero,potential_zero,potential_zero]
      change (∑ j, Bnew j)*SimplexTracker.movement a a₀ ≤
        0-potential q Bnew a+(0-0)+
        15*scale q*(∑ i, |Bnew i-0|)+4*((∑ i, Bnew i)-(∑ _i : ι, (0:ℝ)))
      simp only [sub_zero,sub_self,add_zero,sum_const_zero]
      rw [hsum]
      linarith [le_abs_self (potential q Bnew a)]
  | some p =>
    cases q with
    | none =>
      have hz := zero_supported hqB
      have hn := zero_supported hqN
      refine ⟨fun _ => 0,fun _ => 0,rfl,rfl,?_,?_,?_⟩
      · intro i; simp [hn,eta]
      · intro i; simp [hz]
      · simp [hz,hn,potential,scale,AdaptiveAlpha.potential_zero]
    | some q => exact AdaptiveAlpha.step hp hq Bstar Bnew a₀ hB hBn hST hpB hqB hqN ha₀

end UniformKServer.AlphaEmpty

end


end

end OAI
