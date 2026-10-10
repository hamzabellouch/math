import Mathlib
import OAI.Algebra.GroupRing.TypedGraphs

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageEntropy

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ)
    (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)
    (d : Underlying s len → ℤ)

/-- The literal label/bin exponent, in the stage bound. -/
def labelCost (j : ℕ) : ℝ :=
  (∑ c : StageLabels.activeComponents
    (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk (activeBlocks s len m j),
      ActualStageLabels.cost s hs len m cmp err d c.val) -
    ∑ i ∈ activeBlocks s len m j, (d i : ℝ)

theorem labelCost_eq (M : ℕ) (j : Fin M) :
    labelCost s hs len m cmp err d j =
      LinkComponents.stageCost (multiplicity s len m) (ActualStageLabels.P s hs len m cmp err)
        M (fun i => (d i : ℝ)) (1/600) s j := by
  unfold labelCost
  change (∑ c : StageLabels.activeComponents
    (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk
    (Finset.univ.filter (fun i => j.val < multiplicity s len m i)),
      ActualStageLabels.cost s hs len m cmp err d c.val) - _ = _
  rw [ActualStageLabels.cost_sum]
  simp only [activeBlocks,Finset.sum_filter,LinkComponents.stageCost,
    ActualStageLabels.cost,RepeatedBlocks.multiplicity]
  rw [sub_eq_add_neg]
  rw [add_comm]
  congr! 3

/-- The source uniform block-propagation and chain-tail error, before taking
limits. All blocks and both sides are counted only once. -/
def looseCost : ℝ :=
  (2*(err : ℝ)*Fintype.card (Underlying s len)+(s+1)*Fintype.card C)*
    Real.log (Fintype.card Letter)

/-- Literal component costs dispatched through proven unmatched-incidence
and layer-cake estimates. The power hypothesis is the (separate) actual
immersed-path vertex/edge inequality, not a first-moment assumption. -/
theorem sum_exponents (M : ℕ) (hm : ∀ c, m c ≤ M) (a logn : ℝ)
    (power error : Fin M → ℝ) (ha : 0≤a) (hn : 0≤logn)
    (hlow : ∀ i, (1/600:ℝ)*s/2 ≤ d i) (hhigh : ∀ i, (d i : ℝ) ≤ a*s)
    (hpower : ∑ j, power j ≤ 0) :
    (Finset.univ.sum (fun j : Fin M => power j*logn + labelCost s hs len m cmp err d j.val + error j)) ≤
      a*s*Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched -
        (1/1200:ℝ)*s*(∑ i : Underlying s len, (multiplicity s len m i : ℝ)) +
          ∑ j : Fin M, error j := by
  simp_rw [labelCost_eq]
  convert LinkComponents.sum_stageBound (multiplicity s len m)
    (ActualStageLabels.P s hs len m cmp err) M (fun i => hm i.1)
    (fun i => (d i : ℝ)) (1/600) s a logn power error
    (by norm_num) hs.le ha hn hlow hhigh hpower using 1
  norm_num
  left
  congr! 3

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate TwoSideFullStage
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)
variable (firstA lastA : CA m j → VA) (firstB lastB : CB m j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)
local notation "SA" => sideA len m j firstA lastA outA pinA
local notation "SB" => sideB len m j firstB lastB outB pinB

/-- A complete literal-stage first moment, with its signed vertex exponent
and the source denominator, without stage independence. -/
theorem mean_bound (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (err K Q rep : ℕ)
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep) (hr : 0<StageDenominator.denominator K rep)
    (hA : TwoSideStage.Conditions SA (TypedGraphs.size rep) (129/16513)
      (3*GirthAsymptotics.L (TypedGraphs.size rep)) 132 (StageDenominator.denominator K rep))
    (hB : TwoSideStage.Conditions SB (TypedGraphs.size rep) (129/16513)
      (3*GirthAsymptotics.L (TypedGraphs.size rep)) 132 (StageDenominator.denominator K rep))
    (hlen : ∀ c,0<len c) (hQ : Fintype.card (CA m j)+Fintype.card (CB m j)≤Q)
    (hE : (SA).edges+(SB).edges ≤ K*GirthAsymptotics.L (TypedGraphs.size rep)) :
    TwoSideMean.mean (((SA).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))) ×ˢ
      ((SB).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))))
      (TwoSideStage.count SA SB (fullWords s len m j cmp d)
        (restrictA len m j) (restrictB len m j)) ≤
      Real.exp (((((SA).freeMarks+(SB).freeMarks:ℕ):ℝ)-
        (Fintype.card (CA m j)+Fintype.card (CB m j):ℕ))*Real.log (TypedGraphs.size rep) +
          labelCost s hs len m cmp err d j + looseCost s len err + StageDenominator.error K Q rep) := by
  have hm := TwoSideFullStage.mean_bound s hs len m j firstA lastA firstB lastB
    outA outB pinA pinB cmp d err hlarge hscale hreduced
    (TypedGraphs.size rep) (129/16513) _ 132 _ hA hB
  have hc := StageDenominator.joint_cost_bound SA SB K Q rep hn hr
    (fun c => hlen (.inl c.val)) (fun c => hlen (.inr c.val)) hQ hE
  apply hm.trans
  apply (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  unfold labelCost looseCost
  change (((((SA).freeMarks+(SB).freeMarks:ℕ):ℝ)-
    (Fintype.card (CA m j)+Fintype.card (CB m j):ℕ))*Real.log (TypedGraphs.size rep)+
      StageDenominator.error K Q rep) + _ = _
  ring

end TorsionFreeZeroDivisors.StageEntropy

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*} (D : OccurrenceMatching.Data (Ω := Ω) (B := B) (E := E))

def transportUnmatched (r : B' ≃ B) : (D.transport r).matching.Unmatched ≃ D.matching.Unmatched where
  toFun o := ⟨r o.val,by
    rw [← D.transport_partner r o.val,o.property]⟩
  invFun o := ⟨r.symm o.val,by
    apply r.injective
    rw [D.transport_partner,r.apply_symm_apply,o.property]⟩
  left_inv o := Subtype.ext (r.symm_apply_apply o.val)
  right_inv o := Subtype.ext (r.apply_symm_apply o.val)

variable [Fintype B]
theorem card_unmatched : Fintype.card D.matching.Unmatched = D.unmatchedBlocks.card := by
  change Fintype.card {o : B // D.matching.partner o = o} = _
  rw [Fintype.card_subtype]
  rfl
end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.StageMass

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ)
  (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def totalLength : ℝ := ∑ t : Traversal m, (traversalLength len m t : ℝ)
def uncovered : ℕ := (cmp.matchingData s hs (traversalLength len m) err).unpairedPositions.card

theorem unmatched_card : Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched =
    (cmp.matchingData s hs (traversalLength len m) err).unmatchedBlocks.card := by
  rw [← OccurrenceMatching.Data.card_unmatched]
  convert Fintype.card_congr
    ((cmp.matchingData s hs (traversalLength len m) err).transportUnmatched (occurrenceEquiv s len m).symm) using 1 <;> congr! 3

variable [Fintype E]
/-- The occurrence involution used by the entropy components has exactly the
unmatched mass of the literal half-integer comparisons. -/
theorem unmatched_bound (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err) :
    s*Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched ≤
      uncovered s hs len m cmp err + 22*s*Fintype.card E + totalLength len m/s := by
  rw [unmatched_card]
  exact cmp.unmatched_bound s hs (traversalLength len m) err ν hsmall herr

omit [Fintype E] in
/-- Repeated traversal length is counted with its actual multiplicity. -/
theorem totalLength_eq : totalLength len m = ∑ c, (m c:ℝ)*len c := by
  simp only [totalLength,Fintype.sum_sigma,traversalLength,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

omit [Fintype E] in
theorem fullMass_eq : (∑ i : Underlying s len, (multiplicity s len m i:ℝ)) =
    ∑ c, (blockCount s (len c):ℝ)*m c := by
  simp only [Underlying,Block,Fintype.sum_sigma,RepeatedBlocks.multiplicity,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

omit [Fintype E] in
include hs in
/-- The only mass lost from full blocks is at the ends of actual chain
traversals. In particular repeated paths do not reduce this loss count. -/
theorem fullMass_lower : totalLength len m ≤
    s*(∑ i : Underlying s len, (multiplicity s len m i:ℝ)) + s*(∑ c,(m c:ℝ)) := by
  rw [totalLength_eq,fullMass_eq,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  have h := mul_le_mul_of_nonneg_left (count_bound s hs (len c)).2.le (Nat.cast_nonneg (m c): (0:ℝ) ≤ m c)
  nlinarith

omit [Fintype E] in
include hs in
theorem fullMass_lower_bounded (M Q : ℕ) (hm : ∀ c,m c≤M) (hQ : Fintype.card C≤Q) :
    totalLength len m ≤ s*(∑ i : Underlying s len, (multiplicity s len m i:ℝ)) + s*(M:ℝ)*Q := by
  have hm' : (∑ c,(m c:ℝ)) ≤ (M:ℝ)*Q := by
    calc
      _ ≤ ∑ _c : C,(M:ℝ) := Finset.sum_le_sum (fun c _ => by exact_mod_cast hm c)
      _ = (M:ℝ)*Fintype.card C := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hQ) (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left hm' hs.le
  have hmass := fullMass_lower s hs len m
  nlinarith

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] [Fintype E]
  (s : ℝ) (hs : 0<s) (len m : C → ℕ)
  (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def residual (M Q : ℕ) (denError : ℝ) : ℝ :=
  256*(22*s*Fintype.card E+totalLength len m/s) +
    (1/1200:ℝ)*s*M*Q + M*(StageEntropy.looseCost s len err+denError)

/-- All explicit finite stage losses, before the common-scale limit. -/
theorem exponent_sum_bound (M Q : ℕ) (hm : ∀ c,m c≤M) (hQ : Fintype.card C≤Q)
    (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err)
    (d : Underlying s len → ℤ) (hlow : ∀ i,(1/600:ℝ)*s/2≤d i)
    (hhigh : ∀ i,(d i:ℝ)≤256*s)
    (logn denError : ℝ) (hn : 0≤logn) (power : Fin M → ℝ)
    (hpower : ∑ j,power j≤0) :
    (Finset.univ.sum (fun j : Fin M => power j*logn+
      StageEntropy.labelCost s hs len m cmp err d j.val+
      (StageEntropy.looseCost s len err+denError))) ≤
        -(1/1200:ℝ)*totalLength len m + 256*uncovered s hs len m cmp err+
          residual (E := E) s len m err M Q denError := by
  have h := StageEntropy.sum_exponents s hs len m cmp err d M hm 256 logn power
    (fun _ => StageEntropy.looseCost s len err+denError) (by norm_num) hn hlow hhigh hpower
  have hu := unmatched_bound s hs len m cmp err ν hsmall herr
  have hf := fullMass_lower_bounded s hs len m M Q hm hQ
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  unfold residual
  linarith

/-- Concrete finite selection input: only an actual uncovered-length bound
and the independently controlled remainder are needed. -/
theorem decay (M Q : ℕ) (hm : ∀ c,m c≤M) (hQ : Fintype.card C≤Q)
    (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err)
    (d : Underlying s len → ℤ) (hlow : ∀ i,(1/600:ℝ)*s/2≤d i)
    (hhigh : ∀ i,(d i:ℝ)≤256*s)
    (logn denError : ℝ) (hn : 0≤logn) (power : Fin M → ℝ)
    (hpower : ∑ j,power j≤0)
    (hb : (uncovered s hs len m cmp err:ℝ) ≤ StageFusion.epsilon (1/600) 256*totalLength len m)
    (he : residual (E := E) s len m err M Q denError ≤ totalLength len m/4800) :
    (Finset.univ.sum (fun j : Fin M => power j*logn+
      StageEntropy.labelCost s hs len m cmp err d j.val+
      (StageEntropy.looseCost s len err+denError))) ≤ -totalLength len m/2400 := by
  have h := exponent_sum_bound s hs len m cmp err M Q hm hQ ν hsmall herr
    d hlow hhigh logn denError hn power hpower
  have hH : 0≤totalLength len m := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have ha := StageFusion.absorb_errors (δ := 1/600) (a := 256) (by norm_num) (by norm_num) hH hb
    (by linarith : residual (E := E) s len m err M Q denError ≤ (1/600:ℝ)*totalLength len m/8)
  linarith
end TorsionFreeZeroDivisors.StageMass

namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

def values (s : ℝ) : Finset ℤ := Finset.Icc 0 ⌊256*s⌋
def profiles {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ) : Finset (Underlying s len → ℤ) :=
  Fintype.piFinset (fun _ => values s)

theorem mem_values {h : ℕ} (hh : 3002 ≤ h) (s : ℝ) (hs : 0 ≤ s)
    (hscale : s+1200 ≤ 2*h) (hscale' : (h:ℝ) ≤ 2*s)
    (d : ℤ) (W : Fin h → Letter) (hW : W∈binWords h d) : d∈values s := by
  obtain ⟨hl,hu,_⟩ := bin_full_bounds h hh s hscale hscale' d W hW
  have hd : (0:ℝ)≤d := (by positivity : (0:ℝ) ≤ (1/600:ℝ)*s/2).trans hl
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hd,Int.le_floor.mpr hu⟩

theorem card_values (s : ℝ) (hs : 0 ≤ s) : ((values s).card:ℝ) ≤ 256*s+1 := by
  have hf : (0:ℤ)≤⌊256*s⌋ := Int.floor_nonneg.mpr (by positivity)
  have hcast : ((⌊256*s⌋+1).toNat:ℝ) = (⌊256*s⌋:ℝ)+1 := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega),Int.cast_add,Int.cast_one]
  simp only [values,Int.card_Icc,sub_zero]
  rw [hcast]
  linarith [Int.floor_le (256*s)]

variable {C : Type*} [Fintype C]
theorem card_profiles (s : ℝ) (len : C → ℕ) (hs : 0 ≤ s) :
    ((profiles s len).card:ℝ) ≤ Real.exp (Fintype.card (Underlying s len)*Real.log (256*s+1)) := by
  have hp : 0<256*s+1 := by positivity
  rw [profiles,Fintype.card_piFinset,Finset.prod_const,Finset.card_univ,Nat.cast_pow]
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (card_values s hs) _).trans_eq
  rw [Real.exp_nat_mul,Real.exp_log hp]

/-- The number of all integer bin assignments is exponentially bounded by the
actual full-block mass. There is no independence assumption between bins. -/
theorem cardinal_bound (s : ℝ) (hs : 0<s) (len : C → ℕ) :
    ((profiles s len).card:ℝ) ≤ Real.exp
      (((∑ c,(len c:ℝ))/s)*Real.log (256*s+1)) := by
  apply (card_profiles s len hs.le).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right
  · exact (le_div_iff₀ hs).mpr (by simpa [mul_comm] using Comparisons.block_mass s hs len)
  · exact Real.log_nonneg (by linarith)
end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.GridAsymptotics
open Filter Topology
open scoped Classical

def exponent (d : ℕ) : ℝ := 1 / (2*((d : ℝ)+1))
def N (d : ℕ) (L : ℝ) : ℕ := ⌊L ^ exponent d⌋₊
def R (d : ℕ) (L : ℝ) : ℕ := ⌊Real.sqrt (N d L)⌋₊

theorem exponent_pos (d : ℕ) : 0 < exponent d := by unfold exponent; positivity

theorem N_pos (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : 0 < N d L := by
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow hL (exponent_pos d).le

theorem R_pos (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : 0 < R d L := by
  apply Nat.floor_pos.mpr
  apply Real.le_sqrt_of_sq_le
  norm_num
  exact_mod_cast N_pos d hL

theorem R_le_N (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : R d L ≤ N d L := by
  apply Nat.floor_le_of_le
  apply Real.sqrt_le_iff.mpr
  have hn : (1 : ℝ) ≤ N d L := by exact_mod_cast N_pos d hL
  constructor <;> nlinarith

theorem denominator_le_sqrt (d : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    ((N d L : ℝ)^d * R d L) ≤ Real.sqrt L := by
  have hn : (N d L : ℝ) ≤ L ^ exponent d := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
  have hr : (R d L : ℝ) ≤ N d L := by exact_mod_cast R_le_N d hL
  calc
    _ ≤ (N d L : ℝ)^d * N d L := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (N d L : ℝ)^(d+1) := (pow_succ _ _).symm
    _ ≤ (L ^ exponent d)^(d+1) := pow_le_pow_left₀ (by positivity) hn _
    _ = L ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ L)]
      congr 1
      push_cast
      unfold exponent
      field_simp
    _ = Real.sqrt L := (Real.sqrt_eq_rpow _).symm

def scale (d : ℕ) (L : ℝ) (u : ℕ) : ℝ := L / ((u : ℝ)*R d L)

theorem scale_bounds (d : ℕ) {L : ℝ} (hL : 1 ≤ L) {u : ℕ}
    (hu : 1 ≤ u) (hub : u ≤ (N d L)^d) :
    Real.sqrt L ≤ scale d L u ∧ scale d L u / L ≤ 1/(R d L : ℝ) := by
  have hLp : 0 < L := by linarith
  have hRp : (0 : ℝ) < R d L := by exact_mod_cast R_pos d hL
  have hup : (0 : ℝ) < u := by exact_mod_cast hu
  have huR : ((u : ℝ)*R d L) ≤ Real.sqrt L := by
    have hubr : (u : ℝ) ≤ (N d L : ℝ)^d := by exact_mod_cast hub
    apply le_trans (mul_le_mul_of_nonneg_right hubr hRp.le)
    simpa using denominator_le_sqrt d hL
  constructor
  · unfold scale
    apply (le_div_iff₀ (mul_pos hup hRp)).mpr
    have hs := Real.sq_sqrt hLp.le
    have ht := mul_le_mul_of_nonneg_left huR (Real.sqrt_nonneg L)
    nlinarith
  · have hs : scale d L u ≤ L / (R d L : ℝ) := by
      unfold scale
      apply div_le_div_of_nonneg_left hLp.le hRp
      have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
      nlinarith
    apply (div_le_iff₀ hLp).mpr
    simpa [div_eq_mul_inv,mul_comm] using hs

theorem N_tendsto (d : ℕ) : Tendsto (fun L : ℝ => (N d L : ℝ)) atTop atTop := by
  exact (tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop).comp
    (tendsto_rpow_atTop (exponent_pos d))

theorem R_tendsto (d : ℕ) : Tendsto (fun L : ℝ => (R d L : ℝ)) atTop atTop := by
  exact (tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop).comp
    (Real.tendsto_sqrt_atTop.comp (N_tendsto d))

theorem alignment_error_tendsto (d : ℕ) :
    Tendsto (fun L : ℝ => (R d L : ℝ)/(N d L : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun L : ℝ => 1 / Real.sqrt (N d L)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (N_tendsto d))
  apply squeeze_zero' (Eventually.of_forall (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (eventually_atTop.mpr ⟨1,fun L hL => ?_⟩) hupper
  have hn : (0 : ℝ) < N d L := by exact_mod_cast N_pos d hL
  have hs := Real.sqrt_pos.mpr hn
  have hr : (R d L : ℝ) ≤ Real.sqrt (N d L) := Nat.floor_le (Real.sqrt_nonneg _)
  apply (div_le_div_iff₀ hn hs).mpr
  have ht := mul_le_mul_of_nonneg_right hr hs.le
  have he := Real.sq_sqrt hn.le
  nlinarith

/-- Exactly the source compatibility test, before choosing the least u. -/
def Compatible (d : ℕ) (L : ℝ) (offset : Fin d → ℤ) (u : ℕ) : Prop :=
  1 ≤ u ∧ ∃ z : Fin d → ℤ, ∀ i,
    |(u : ℝ)*((offset i : ℝ)/L)-(z i : ℝ)| < 1/(N d L : ℝ)

theorem compatible_exists (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    ∃ u, Compatible d L offset u := by
  obtain ⟨u,hu,_,z,hz⟩ := BlockGrid.simultaneous (N_pos d hL) (fun i => (offset i : ℝ)/L)
  exact ⟨u,hu,z,hz⟩

def chosenU (d : ℕ) (L : ℝ) (offset : Fin d → ℤ) : ℕ :=
  if hL : 1 ≤ L then Nat.find (compatible_exists d hL offset) else 1

theorem chosen_spec (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    Compatible d L offset (chosenU d L offset) := by
  unfold chosenU
  rw [dite_eq_left hL]
  exact Nat.find_spec _

theorem chosen_min (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) {v : ℕ}
    (hv : Compatible d L offset v) : chosenU d L offset ≤ v := by
  unfold chosenU
  rw [dite_eq_left hL]
  exact Nat.find_min' _ hv

theorem chosen_bound (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    chosenU d L offset ≤ (N d L)^d := by
  obtain ⟨u,hu,hub,z,hz⟩ := BlockGrid.simultaneous (N_pos d hL) (fun i => (offset i : ℝ)/L)
  exact (chosen_min d hL offset ⟨hu,z,hz⟩).trans hub

def chosenScale (d : ℕ) (L : ℝ) (offset : Fin d → ℤ) : ℝ :=
  scale d L (chosenU d L offset)

theorem chosen_alignment (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    ∃ ν : Fin d → ℤ, ∀ i,
      |(offset i : ℝ)/chosenScale d L offset-(ν i : ℝ)| < (R d L : ℝ)/(N d L) := by
  obtain ⟨hu,z,hz⟩ := chosen_spec d hL offset
  refine ⟨fun i => (R d L : ℤ)*z i,fun i => ?_⟩
  have hLp : L ≠ 0 := ne_of_gt (by linarith : 0 < L)
  have hR : (0 : ℝ) < R d L := by exact_mod_cast R_pos d hL
  have hh := mul_lt_mul_of_pos_left (hz i) hR
  have he : (offset i : ℝ)/chosenScale d L offset-((R d L : ℤ)*z i : ℤ) =
      (R d L : ℝ)*((chosenU d L offset : ℝ)*((offset i : ℝ)/L)-(z i : ℝ)) := by
    simp only [chosenScale,scale,Int.cast_mul,Int.cast_natCast]
    field_simp
  rw [he,abs_mul,abs_of_pos hR]
  simpa [div_eq_mul_inv,mul_assoc] using hh

/-- Uniformly over arbitrary schedules of all prescribed offsets. -/
theorem scale_tendsto (d : ℕ) (offset : ℝ → Fin d → ℤ) :
    Tendsto (fun L => chosenScale d L (offset L)) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ Real.tendsto_sqrt_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  exact (scale_bounds d hL (chosen_spec d hL (offset L)).1 (chosen_bound d hL (offset L))).1

theorem relative_scale_tendsto (d : ℕ) (offset : ℝ → Fin d → ℤ) :
    Tendsto (fun L => chosenScale d L (offset L)/L) atTop (𝓝 0) := by
  have hu : Tendsto (fun L : ℝ => 1/(R d L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (R_tendsto d)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact div_nonneg (div_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact (scale_bounds d hL (chosen_spec d hL (offset L)).1 (chosen_bound d hL (offset L))).2

/-- Relative errors for lost cut blocks plus rounded block lengths. -/
theorem grid_loss_tendsto (d : ℕ) (offset : ℝ → Fin d → ℤ) :
    Tendsto (fun L => chosenScale d L (offset L)/L + 1/chosenScale d L (offset L)) atTop (𝓝 0) := by
  have hi : Tendsto (fun L => (1 : ℝ)/chosenScale d L (offset L)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (scale_tendsto d offset)
  simpa using (relative_scale_tendsto d offset).add hi

/-- A fixed integer loss shared by all comparison sides. -/
def letterError (d : ℕ) (L : ℝ) (offset : Fin d → ℤ) : ℕ :=
  ⌈2*((R d L : ℝ)/(N d L))*chosenScale d L offset+4⌉₊

theorem chosenScale_pos (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    0 < chosenScale d L offset := by
  exact lt_of_lt_of_le (Real.sqrt_pos.mpr (by linarith))
    (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1

theorem letterError_bounds (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    2*((R d L : ℝ)/(N d L))*chosenScale d L offset+4 ≤ letterError d L offset ∧
    (letterError d L offset : ℝ) ≤
      2*((R d L : ℝ)/(N d L))*chosenScale d L offset+5 := by
  constructor
  · exact Nat.le_ceil _
  · have hs := chosenScale_pos d hL offset
    have hh := Nat.ceil_lt_add_one (show 0 ≤
        2*((R d L : ℝ)/(N d L))*chosenScale d L offset+4 by
        positivity)
    dsimp only [letterError]
    linarith

theorem uniform_alignment (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    ∃ ν : Fin d → ℤ, ∀ i,
      2*|(offset i : ℝ)-(ν i : ℝ)*chosenScale d L offset|+4 ≤ letterError d L offset := by
  obtain ⟨ν,hν⟩ := chosen_alignment d hL offset
  refine ⟨ν,fun i => ?_⟩
  have hs := chosenScale_pos d hL offset
  have hh := (mul_lt_mul_of_pos_right (hν i) hs).le
  have he : |(offset i : ℝ)/chosenScale d L offset-(ν i : ℝ)| *chosenScale d L offset =
      |(offset i : ℝ)-(ν i : ℝ)*chosenScale d L offset| := by
    rw [← abs_of_pos hs,← abs_mul]
    congr 1
    rw [abs_of_pos hs]
    field_simp
  rw [he] at hh
  have hr := (letterError_bounds d hL offset).1
  nlinarith

theorem relative_error_tendsto (d : ℕ) (offset : ℝ → Fin d → ℤ) :
    Tendsto (fun L => (letterError d L (offset L) : ℝ)/chosenScale d L (offset L)) atTop (𝓝 0) := by
  have hi : Tendsto (fun L => (5 : ℝ)/chosenScale d L (offset L)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (scale_tendsto d offset)
  have hu : Tendsto (fun L => 2*((R d L : ℝ)/(N d L))+5/chosenScale d L (offset L)) atTop (𝓝 0) := by
    simpa using ((alignment_error_tendsto d).const_mul 2).add hi
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact div_nonneg (Nat.cast_nonneg _) (chosenScale_pos d hL (offset L)).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hs := chosenScale_pos d hL (offset L)
    apply (div_le_iff₀ hs).mpr
    have hh := (letterError_bounds d hL (offset L)).2
    have he : (2*((R d L : ℝ)/(N d L))+5/chosenScale d L (offset L))*chosenScale d L (offset L) =
        2*((R d L : ℝ)/(N d L))*chosenScale d L (offset L)+5 := by
      field_simp
    rwa [he]

theorem eventually_small_error (d : ℕ) (offset : ℝ → Fin d → ℤ) :
    ∀ᶠ L in atTop, 2*(letterError d L (offset L) : ℝ) < chosenScale d L (offset L)-1 := by
  have hfrac := (relative_error_tendsto d offset).eventually (gt_mem_nhds (show (0 : ℝ) < 1/4 by norm_num))
  have hlarge := (scale_tendsto d offset).eventually (eventually_gt_atTop (2 : ℝ))
  filter_upwards [hfrac,hlarge] with L hL hs
  have hh := (div_lt_iff₀ (show 0 < chosenScale d L (offset L) by linarith)).mp hL
  linarith

end TorsionFreeZeroDivisors.GridAsymptotics

end

end OAI
