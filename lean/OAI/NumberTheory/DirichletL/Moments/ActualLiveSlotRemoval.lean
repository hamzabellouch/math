import OAI.NumberTheory.DirichletL.Moments.PrimeSlotExternal
import OAI.NumberTheory.DirichletL.Moments.SlotNormalization

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentActualLiveSlotRemoval
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotExternal CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_live_slot_removal {ι:Type*} [Fintype ι] [DecidableEq ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hε:0<ε)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀(J:Finset ι) (w:ι→ℝ) (F mesh:ℝ),0≤F → 0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
      ∃R:Finset ι,R⊆J ∧ (R=J ∨ F≤6*κ*(∑i∈R,w i)) ∧
      κ*(∑i∈R,w i)≤F/6+κ*mesh ∧
      ∀Z:ℝ,Z₀≤Z → ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M →
      m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod → ¬FixedInducingRow η Q m A z →
      ∀(σ ν:ι→ℝ) (t V:ℝ), (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|ν i|≤V) →
      ∀(W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i=>annularWeight (W i) (P i) (σ i) (ν i)
      ‖selectedProduct J η m A z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+F/6+κ*mesh)*
          ‖selectedProduct (J\R) η m A z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0<loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=actual_slots_external_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  have hκpos:0<κ:=by linarith
  refine ⟨degree*N,C^N,Z₀,pow_pos (zero_lt_one.trans_le hC) _,hZ₀,?_⟩
  intro J w F mesh hF hmesh hw hwm hwcap
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w F κ mesh hF hκpos hmesh
    (fun i _=>hw i) (fun i _=>hwm i)
  refine ⟨R,hR,hpay,hcost,?_⟩
  intro Z hZ η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ ν t V hσ hσhi hV hν W₁ W₂ X₁ X₂
  dsimp only
  have hz1:1≤Z:=hZ₀.le.trans hZ
  have hz0:0<Z:=zero_lt_one.trans_le hz1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤Z^loss:=Real.one_le_rpow hz1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η m A z (primePool M H (b i) (Z^(w i)))
      (annularWeight (W i) (Z^(w i)) (σ i) (ν i)) t (Z^(w i))‖^2≤B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound i Z (Z^(w i)) hZ (Real.one_le_rpow hz1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hz1 (hwcap i)) η Q m A z hQ hm hA hz hmLam hm2 hcond hex
      (σ i) t (ν i) V (hσ i) (hσhi i) (hν i)
    rw [←Real.rpow_mul hz0.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η m A z W₁ W₂
    (fun i=>primePool M H (b i) (Z^(w i))) (fun i=>annularWeight (W i) (Z^(w i)) (σ i) (ν i))
    (fun i=>Z^(w i)) t X₁ X₂ Z κ hz0 w (fun _=>B) (fun i hi=>zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤Z^(F/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hz1 hcost
  have hsplit:B^N=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hz0.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
    _≤B^N*Z^(F/6+κ*mesh):=mul_le_mul hpow hcostZ (Real.rpow_nonneg hz0.le _) (by positivity)
    _=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)+(F/6+κ*mesh)):=by
      rw [hsplit,mul_assoc,←Real.rpow_add hz0]
    _≤_:=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (by positivity)

  apply le_of_eq
  congr 3
  ext i
  simp

end SevenEighths.CenteredMomentActualLiveSlotRemoval

end

end OAI
