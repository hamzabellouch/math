import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperTyped

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

 theorem machine_cons {n k : ℕ} (M : BitMachine) (c e L : ℕ) (d : RationalMetric n) (hk : 0<k)
    (t : ℕ) (z : MachineState M) (s : Configuration n k) (r : Fin n) (w : List (Fin n)) :
    machineExpectedCost M c e L d hk t z s (r::w)=
      BitSampling.mean (fun coins : Fin (requestBudget c e L (t+1))→Bool=>
        let z':=requestStep M c e L (t+1) z r coins
        let j:=selectedLabel hk z'
        (d.distance (s j) r:ℝ)+machineExpectedCost M c e L d hk (t+1) z' (serve s r j) w) := by
  simp only [machineExpectedCost,BitSampling.mean,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat]

abbrev tcExpected {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (d : RationalMetric n) (a : TC n k v) (s : Configuration n k) (w : List (Fin n)) :=
  TapeController.expected hk hR d (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
    (tcRows hk v) (tcN hk v hT) a s w

 theorem active_expected {n k : ℕ} (mult L : ℕ) (hk : 0<k) (hkn : k≤n)
    (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (d : RationalMetric n) (w : List (Fin n))
    (t : ℕ) (ht : 2^c.2≤t) (a : TC n k v) (z : MachineState (machine mult))
    (hz : represents mult v c a z) (s : Configuration n k) :
    machineExpectedCost (machine mult) 64 1 L d hk t z s w=
      tcExpected hk hkn v hR hT d a s w := by
  induction w generalizing t a z s with
  | nil=>rfl
  | cons r w ih=>
    have htime:=process_bound L t c.2 t ht le_rfl
    have hstep:=typed_step mult L t hk hkn v hR hT c hc a z hz htime r
    rw [machine_cons]
    change _=BitSampling.mean (fun bs : TapeController.Tape k (cap v) (bits v)=>
      (d.distance (s (tcLabel hk v hT a r bs)) r:ℝ)+
        tcExpected hk hkn v hR hT d (tcNext hk hkn v hR hT a r bs)
          (serve s r (tcLabel hk v hT a r bs)) w)
    have he : ∀coins : Fin (requestBudget 64 1 L (t+1))→Bool,
        let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
        let bs:=tapeCoins (sample_bound L t n k v c hc htime) coins
        (d.distance (s (selectedLabel hk z')) r:ℝ)+
          machineExpectedCost (machine mult) 64 1 L d hk (t+1) z' (serve s r (selectedLabel hk z')) w=
        (d.distance (s (tcLabel hk v hT a r bs)) r:ℝ)+
          tcExpected hk hkn v hR hT d (tcNext hk hkn v hR hT a r bs)
            (serve s r (tcLabel hk v hT a r bs)) w := by
      intro coins
      dsimp only
      rw [(hstep coins).2.1]
      rw [ih (t+1) (by omega) _ _ (hstep coins).1]
    simp_rw [he]
    simpa only using (tapeCoins_mean (sample_bound L t n k v c hc htime)
      (fun bs : TapeController.Tape k (cap v) (bits v)=>
        (d.distance (s (tcLabel hk v hT a r bs)) r:ℝ)+
          tcExpected hk hkn v hR hT d (tcNext hk hkn v hR hT a r bs)
            (serve s r (tcLabel hk v hT a r bs)) w))

end UniformKServer.UniformWrapper

end

end OAI
