import OAI.NumberTheory.TotientAsymptotic.ActualClassSum
import OAI.NumberTheory.TotientAsymptotic.CollisionChoiceAbsorption
import OAI.NumberTheory.TotientAsymptotic.CollisionGridCount

namespace OAI

/-! Complete comparison summation for distinct actual suffix representatives. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

theorem actual_block_count (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    ∀ (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H))),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _) →
    (Q.card : ℝ) ≤ y/Real.log y*Real.exp (-B y/(8*((m x-i : ℕ) : ℝ)^4)) := by
  obtain ⟨C,M,y₀,hC,hM,hy₀,hsum⟩ := actual_survivor_class_sum hford hmertens
  let A := 6*(|Real.log C|+26)
  let K := A+3*|Real.log M|+61
  refine ⟨y₀,hy₀,?_⟩
  filter_upwards [hsum,collision_kernel_domain,collision_normality_domain,collision_grid_card_uniform,
    ford_band_absorbs_square K] with H hsum hkern hnormal hgrid habs
  filter_upwards [hsum,hkern,hnormal,hgrid,habs] with x hs hk hn hg ha
  intro i hi hL hR t y hy hBy hlo hup Q hQ hdet
  have hy1 : 1 < y := hy₀.trans_le hy
  obtain ⟨hh,hlog,_,hlogB,_,hZ,hZu,hcut⟩ := hk i hi hL hR y hy1 hBy hlo hup
  have hhalf : fordBandScale x i/2 ≤ B y := by
    have hbi : 0 < fordBandScale x i := by
      have hratio := hup
      linarith
    linarith
  obtain ⟨hS,hBS,hSy⟩ := hn i hi y hy1 hhalf
  have hS1 : 1 < normalityScale x i :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBy1 : 1 ≤ B y := hBS.trans
    (Real.log_le_log (Real.log_pos hS1) (Real.log_le_log (zero_lt_one.trans hS1) hSy))
  let z := collisionSmoothCutoff x i
  let k := collisionLastIndex x i
  let J := collisionCutoff (m x-i)+1
  let h := ((m x-i : ℕ) : ℝ)
  have hz : 1 < z := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
  have hlz : 1 ≤ Real.log z := by
    change 1 ≤ Real.log (Real.exp (Real.exp ((7/10 : ℝ)*fordBandScale x k)))
    rw [Real.log_exp]
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hBz : B z=(7/10 : ℝ)*fordBandScale x k := by
    simp only [z,k,collisionSmoothCutoff,B,Real.log_exp]
  have hZupper : B z ≤ 2*B y/h^18 := by rw [hBz]; exact hZu
  have hNz : 2 ≤ ⌈z⌉₊ := by
    have hz' : 1 < (⌈z⌉₊ : ℝ) := hz.trans_le (Nat.le_ceil z)
    have hz'' : 1 < ⌈z⌉₊ := by exact_mod_cast hz'
    omega
  have hNp := (rounded_prime_endpoint_height hy1 hlog hBy1).1
  let S := (Finset.Icc i k).powerset
  let key := fun q : TotientTuple (R x H) × TotientTuple (R x H) =>
    collisionSurvivors q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i k
  let T := y/Real.log y*Real.exp ((A+3*|Real.log M|+60)*h^2-3*B y/(16*h^4))
  have hylog : 0 ≤ y/Real.log y := div_nonneg (zero_lt_one.trans hy1).le (Real.log_pos hy1).le
  have hJ : (J : ℝ) ≤ h := by dsimp only [J,h]; exact_mod_cast hcut
  have hcount : (Q.card : ℝ) ≤ ∑ _I ∈ S, T := by
    apply finite_class_card_bound Q S key (fun _ => T)
    · intro q _
      exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    · intro I hIS
      have hIsub := Finset.mem_powerset.mp hIS
      have hlen : (Finset.Icc i k).card=J := by
        rw [Nat.card_Icc]
        dsimp [J,k,collisionLastIndex]
        omega
      have hIcard : I.card ≤ m x-i := by
        have ht := Finset.card_le_card hIsub
        rw [hlen] at ht
        exact ht.trans hcut
      have hccard : ((canceledIndices i k I).card : ℝ) ≤ h := by
        have ht : (canceledIndices i k I).card ≤ (Finset.Icc i k).card := Finset.card_le_card (show canceledIndices i k I ⊆ Finset.Icc i k from Finset.sdiff_subset)
        rw [hlen] at ht
        dsimp only [h]
        exact_mod_cast ht.trans hcut
      let F := Q.filter (fun q => key q=I)
      have hF (q) (hq : q ∈ F) := (Finset.mem_filter.mp hq).1
      have hFkey (q) (hq : q ∈ F) := (Finset.mem_filter.mp hq).2
      have hbound := hs i hi hL hR t y hy hBy hlo hup I ⌈z⌉₊ ⌈y+1⌉₊ hNz hNp
        (Nat.le_ceil _) (Nat.le_ceil _) F (fun q hq => hQ q (hF q hq))
        (fun q hq => hFkey q hq) (fun q hq q' hq' he => hdet (hF q hq) (hF q' hq') he)
      have hGbound := hg i hi y hBS hBy1 hup I.card hIcard
      have hcost := collision_all_choice_cost (A := A) (J := 0) hylog hM hBy1
        (by linarith) hlogB hz hlz hZupper
        (by positivity : (0 : ℝ) ≤ (collisionGridFamilies (collisionMesh x y i) I.card).card)
        hGbound hccard (by simpa only [Nat.cast_zero] using (Nat.cast_nonneg (α := ℝ) (m x-i)))
      apply hbound.trans
      apply le_trans _ (by simpa only [pow_zero,one_mul] using hcost)
      apply mul_le_mul_of_nonneg_left (canceled_rounded_mass_power hy1 hlog hBy1)
      exact mul_nonneg (mul_nonneg (mul_nonneg hylog (Real.exp_pos _).le) (by positivity))
        (mul_nonneg hM.le (Real.log_nonneg (hz.le.trans (Nat.le_ceil z))))
  have hT : 0 ≤ T := mul_nonneg hylog (Real.exp_pos _).le
  have hS : S.card=2^J := by
    rw [Finset.card_powerset,Nat.card_Icc]
    congr 1
    dsimp [J,k,collisionLastIndex]
    omega
  calc
    (Q.card : ℝ) ≤ ∑ _I ∈ S, T := hcount
    _ = (2 : ℝ)^J*T := by simp only [Finset.sum_const,nsmul_eq_mul,hS,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ Real.exp (h^2)*T := mul_le_mul_of_nonneg_right (subset_choice_cost (by linarith) hJ) hT
    _ = y/Real.log y*Real.exp (K*h^2-3*B y/(16*h^4)) := by
      dsimp only [T,K]
      rw [show (A+3*|Real.log M|+61)*h^2-3*B y/(16*h^4) =
        h^2+((A+3*|Real.log M|+60)*h^2-3*B y/(16*h^4)) by ring,Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hylog
      apply Real.exp_le_exp.mpr
      have hab := ha i hi (B y) hlo
      change K*h^2 ≤ B y/(16*h^4) at hab
      calc
        K*h^2-3*B y/(16*h^4) ≤ B y/(16*h^4)-3*B y/(16*h^4) := sub_le_sub_right hab _
        _ = -B y/(8*h^4) := by ring

end TotientAsymptotic

end

end OAI
