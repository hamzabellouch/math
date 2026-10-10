import OAI.NumberTheory.DirichletL.Moments.PrimeSlotBound

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentPrimeSlotUniform
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotBound CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_slots_uniform {ι:Type*} [Fintype ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,1≤C ∧ 1<Z₀ ∧ ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t:ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η m A z (primePool M H (b i) P) (slotProfile (W i) P σ) t P‖^2≤
        C*(1+|t|)^degree*Z^loss*P^κ := by
  have hall:=fun i=>actual_slot_all_height_squared M H hH (W i) (a i) (b i) (ha i)
    (hWs i) (hW i) Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  choose degree C Z₀ hC hZ₀ hbound using hall
  let D:ℕ:=∑i,degree i
  let Csum:ℝ:=1+∑i,C i
  let Zsum:ℝ:=2+∑i,Z₀ i
  have hCs:1≤Csum:=by dsimp [Csum]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>(hC i).le))
  have hZs:1<Zsum:=by
    have hh:0≤∑i,Z₀ i:=Finset.sum_nonneg (fun i _=>le_trans zero_le_one (hZ₀ i).le)
    dsimp [Zsum]; linarith
  refine ⟨D,Csum,Zsum,hCs,hZs,?_⟩
  intro i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  have hz0:Z₀ i≤Zsum:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>le_trans zero_le_one (hZ₀ j).le) (Finset.mem_univ i)
    dsimp [Zsum]; linarith
  have hci:C i≤Csum:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Csum]; linarith
  have hdi:degree i≤D:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>Nat.zero_le _) (Finset.mem_univ i)
  have hh:=hbound i Z P (hz0.trans hZ) hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) κ)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hZs.le.trans hZ |>.trans' zero_le_one) loss)
  exact mul_le_mul hci (pow_le_pow_right₀ (by linarith [abs_nonneg t]) hdi)
    (by positivity) (zero_le_one.trans hCs)

end SevenEighths.CenteredMomentPrimeSlotUniform

end

end OAI
