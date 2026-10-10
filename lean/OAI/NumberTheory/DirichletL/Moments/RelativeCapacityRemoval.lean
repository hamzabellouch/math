import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime
import OAI.NumberTheory.DirichletL.Moments.LiveCapacity
import OAI.NumberTheory.DirichletL.Moments.SlotNormalization

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
namespace SevenEighths.CenteredMomentRelativeCapacityRemoval
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily Filter
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem relative_slots_uniform {ι:Type*}[Fintype ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,1≤C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → Q≤(ν i).modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀σ t v V:ℝ,lo≤σ → σ≤hi → 0≤V → |v|≤V →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) P)
        (fun I=>idealCoeff (ν i) I*annularWeight (W i) P σ v I) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  choose degree C hC hb using fun i=>natural_character_slot_bound M H hH (W i) (a i) (b i)
    (ha i) (hWs i) (hW i) Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  let Ctotal:ℝ:=1+∑i,C i
  have hCtotal:1≤Ctotal:=by
    have hsum:=Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>(hC i).le)
    dsimp [Ctotal];linarith
  have hCi (i:ι):C i≤Ctotal:=by
    have hsum:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Ctotal];linarith
  refine ⟨∑i,degree i,Ctotal,hCtotal,?_⟩
  intro ν
  have hev:∀ᶠZ:ℝ in atTop,∀i:ι,_ := Filter.eventually_all.mpr (fun i=>hb i (ν i))
  obtain ⟨Zbase,hbase⟩:=eventually_atTop.mp hev
  refine ⟨max 2 Zbase,lt_max_of_lt_left (by norm_num),?_⟩
  intro i Z P hZ hP hPcap η z hz F hcond Q hQM hQν hex σ t v V hσ hσhi hV hv
  have hZ0:Zbase≤Z:=(le_max_right _ _).trans hZ
  have hZp:0<Z:=lt_of_lt_of_le (by norm_num:0<(2:ℝ)) ((le_max_left _ _).trans hZ)
  refine (hbase Z hZ0 i P hP hPcap η z hz F hcond Q hQM hQν hex σ t v hσ hσhi).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul (hCi i) _ (by positivity) (zero_le_one.trans hCtotal)
  calc
    _≤(1+|t|+V)^(degree i):=pow_le_pow_left₀ (by positivity) (by linarith) _
    _≤_:=pow_le_pow_right₀ (by linarith [abs_nonneg t])
      (Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ i))

theorem actual_relative_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi κ:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → (∀i,Q≤(ν i).modulus) → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*annularWeight (W i) (P i) (σ i) (freq i) I
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0<loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,hC,hbound⟩:=relative_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  have hκpos:0<κ:=by linarith
  refine ⟨degree*N,C^N,pow_pos (zero_lt_one.trans_le hC) _,?_⟩
  intro ν
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound ν
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  let excess:=CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w excess κ mesh (le_max_right _ _) hκpos hmesh
    (fun i _=>hw i) (fun i _=>hwm i)
  refine ⟨R,hR,CenteredMomentLiveCapacity.remaining_capacity J R hR w n₁ n₂ width κ hpay,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQν hex σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
  dsimp only
  have hZ1:1≤Z:=hZ₀.le.trans hZ
  have hZp:0<Z:=zero_lt_one.trans_le hZ1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤Z^loss:=Real.one_le_rpow hZ1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) (Z^(w i)))
      (fun I=>idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I) t (Z^(w i))‖^2≤
      B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound i Z (Z^(w i)) hZ (Real.one_le_rpow hZ1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hZ1 (hwcap i)) η z hz F hcond Q hQM (hQν i) hex
      (σ i) t (freq i) V (hσ i) (hσhi i) hV (hfreq i)
    rw [←Real.rpow_mul hZp.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η fixedBadMask 1 z W₁ W₂
    (fun i=>primePool M H (b i) (Z^(w i)))
    (fun i I=>idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t X₁ X₂ Z κ hZp w (fun _=>B) (fun i hi=>zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤Z^(excess/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hZ1 hcost
  have hsplit:B^N=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hZp.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
    _≤B^N*Z^(excess/6+κ*mesh):=mul_le_mul hpow hcostZ (Real.rpow_nonneg hZp.le _) (by positivity)
    _=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)+(excess/6+κ*mesh)):=by
      rw [hsplit,mul_assoc,←Real.rpow_add hZp]
    _≤_:=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)) (by positivity)
  apply le_of_eq
  congr 3
  ext i
  simp

end SevenEighths.CenteredMomentRelativeCapacityRemoval

end

end OAI
