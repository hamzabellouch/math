import Mathlib
import OAI.Algebra.GroupRing.StageEntropy

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

def rate (d : ℕ) (L : ℝ) : ℝ :=
  1/(R d L:ℝ)+1/Real.sqrt L+(R d L:ℝ)/(N d L)+1/L

theorem rate_nonneg (d : ℕ) {L : ℝ} (hL : 0≤L) : 0≤rate d L := by
  unfold rate
  positivity

theorem rate_tendsto (d : ℕ) : Tendsto (rate d) atTop (𝓝 0) := by
  have hr : Tendsto (fun L : ℝ => 1/(R d L:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (R_tendsto d)
  have hs : Tendsto (fun L : ℝ => 1/Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hi : Tendsto (fun L : ℝ => 1/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  unfold rate
  simpa only [add_zero] using ((hr.add hs).add (alignment_error_tendsto d)).add hi

/-- A single offset-independent rate controls every scalar rounding loss. -/
theorem bounds (d : ℕ) {L : ℝ} (hL : 1≤L) (offset : Fin d → ℤ) :
    chosenScale d L offset/L ≤ rate d L ∧
    1/chosenScale d L offset ≤ rate d L ∧
    (letterError d L offset:ℝ)/chosenScale d L offset ≤ 5*rate d L ∧
    1/L ≤ rate d L := by
  have hL0 : 0<L := by linarith
  have hs := chosenScale_pos d hL offset
  have hroot := Real.sqrt_pos.mpr hL0
  have hb := scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)
  change Real.sqrt L ≤ chosenScale d L offset ∧
    chosenScale d L offset/L ≤ 1/(R d L:ℝ) at hb
  have hi : 1/chosenScale d L offset ≤ 1/Real.sqrt L :=
    one_div_le_one_div_of_le hroot hb.1
  have he : (letterError d L offset:ℝ)/chosenScale d L offset ≤
      2*((R d L:ℝ)/(N d L))+5/chosenScale d L offset := by
    apply (div_le_iff₀ hs).mpr
    have hh := (letterError_bounds d hL offset).2
    have hh' : (2*((R d L:ℝ)/(N d L))+5/chosenScale d L offset)*chosenScale d L offset =
        2*((R d L:ℝ)/(N d L))*chosenScale d L offset+5 := by field_simp
    rwa [hh']
  have hr : 0 ≤ 1/(R d L:ℝ) := by positivity
  have hn : 0 ≤ (R d L:ℝ)/(N d L) := by positivity
  have hlo : 0 ≤ 1/L := by positivity
  have hso : 0 ≤ 1/Real.sqrt L := by positivity
  unfold rate
  simp only [div_eq_mul_inv,one_mul] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

/-- Unlike a chosen offset sequence, this statement is uniform over ALL
integer comparison offsets at each common length scale. -/
theorem eventually_geometry (d : ℕ) : ∀ᶠ L in atTop, ∀ offset : Fin d → ℤ,
    3003 ≤ chosenScale d L offset ∧
    2*(letterError d L offset:ℝ) < chosenScale d L offset-1 := by
  have hr := (rate_tendsto d).eventually_lt_const (by norm_num : (0:ℝ)<1/12)
  have hroot := Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (3003:ℝ))
  filter_upwards [hr,hroot,eventually_ge_atTop (1:ℝ)] with L hr hroot hL offset
  have hb := bounds d hL offset
  have hs := chosenScale_pos d hL offset
  have hlo := (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1
  change Real.sqrt L ≤ chosenScale d L offset at hlo
  have he := (div_le_iff₀ hs).mp hb.2.2.1
  have hi := (div_le_iff₀ hs).mp hb.2.1
  refine ⟨hroot.trans hlo,?_⟩
  nlinarith
end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.StageUniform
open scoped Classical BigOperators Topology
open BlockAlignment ComparedBlocks RepeatedBlocks GridAsymptotics Filter

def alphabetLog : ℝ := Real.log (Fintype.card WordEstimate.Letter)

theorem alphabetLog_nonneg : 0 ≤ alphabetLog := by
  apply Real.log_nonneg
  norm_num [WordEstimate.Letter]

def coefficient (D K M Q : ℕ) : ℝ :=
  256*(22*D+K)+(1/1200:ℝ)*M*Q+M*(10*K+2*Q)*alphabetLog

/-- Uniform scalar estimate. Its inputs are just the explicit common-grid
loss bounds, not an entropy or probability estimate. -/
theorem scalar_bound (D K M Q : ℕ) (L s H blocks err rate den : ℝ)
    (hL : 0 < L) (hs : 0 < s) (_hH : 0 ≤ H) (hb : 0 ≤ blocks)
    (hr : 0 ≤ rate) (hscale : s/L≤ rate) (hinv : 1/s≤ rate)
    (hone : 1/L≤ rate) (he : err/s≤5*rate)
    (hsize : H≤K*L) (hblocks : s*blocks≤K*L) :
    (256*(22*s*D+H/s)+(1/1200:ℝ)*s*M*Q+
      M*((2*err*blocks+(s+1)*Q)*alphabetLog+den))/L ≤
        coefficient D K M Q*rate+M*den/L := by
  have hsl := (div_le_iff₀ hL).mp hscale
  have hon := (div_le_iff₀ hL).mp hone
  have he' := (div_le_iff₀ hs).mp he
  have hHl : H/s ≤ (K:ℝ)*L*rate := by
    calc
      _ ≤ ((K:ℝ)*L)/s := div_le_div_of_nonneg_right hsize hs.le
      _ = ((K:ℝ)*L)*(1/s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  have heb := mul_le_mul_of_nonneg_right he' hb
  have hbc := mul_le_mul_of_nonneg_left hblocks (show 0 ≤ 10*rate by positivity)
  have htail : (s+1)*(Q:ℝ) ≤ 2*rate*L*Q :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg Q)
  have hloss : 2*err*blocks+(s+1)*Q ≤ (10*K+2*Q)*rate*L := by nlinarith
  have hlog := mul_le_mul_of_nonneg_right hloss alphabetLog_nonneg
  have hst := mul_le_mul_of_nonneg_right hsl (show 0 ≤ 22*(D:ℝ) by positivity)
  have hsq := mul_le_mul_of_nonneg_right hsl (show 0 ≤ (1/1200:ℝ)*M*Q by positivity)
  have hM := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)
  apply (div_le_iff₀ hL).mpr
  have hcancel : (coefficient D K M Q*rate+M*den/L)*L =
      coefficient D K M Q*rate*L+M*den := by field_simp
  rw [hcancel]
  unfold coefficient
  nlinarith

variable {C E : Type*} [Fintype C] [Fintype E]

/-- Specialization to the literal stage remainder: the ONLY scale-dependent
upper bound is `rate`, which does not mention offsets or labelled words. -/
theorem residual_bound (K M Q : ℕ) (L : ℝ) (hL : 1≤L)
    (offset : Fin (Fintype.card E) → ℤ) (len m : C → ℕ) (hQ : Fintype.card C≤Q)
    (hH : StageMass.totalLength len m ≤ K*L) (hpositive : ∀ c,1≤ m c) (den : ℝ) :
    StageMass.residual (E := E) (chosenScale (Fintype.card E) L offset) len m
      (letterError (Fintype.card E) L offset) M Q den/L ≤
        coefficient (Fintype.card E) K M Q*GridUniform.rate (Fintype.card E) L+M*den/L := by
  let s := chosenScale (Fintype.card E) L offset
  let err := letterError (Fintype.card E) L offset
  have hs : 0 < s := chosenScale_pos _ hL offset
  have hcard : s*Fintype.card (Underlying s len) ≤ (K:ℝ)*L := by
    apply (Comparisons.block_mass s hs len).trans
    apply le_trans ?_ hH
    rw [StageMass.totalLength_eq]
    apply Finset.sum_le_sum
    intro c _
    have hp : (1:ℝ)≤ m c := by exact_mod_cast hpositive c
    have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (len c): (0:ℝ) ≤ len c)
    simpa only [one_mul] using hm
  have hr := GridUniform.bounds (Fintype.card E) hL offset
  have h := scalar_bound (Fintype.card E) K M Q L s (StageMass.totalLength len m)
    (Fintype.card (Underlying s len)) err (GridUniform.rate (Fintype.card E) L) den
    (by linarith) hs (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    (Nat.cast_nonneg _) (GridUniform.rate_nonneg _ (by linarith))
    hr.1 hr.2.1 hr.2.2.2 hr.2.2.1 hH hcard
  apply le_trans ?_ h
  apply div_le_div_of_nonneg_right _ (by linarith)
  unfold StageMass.residual StageEntropy.looseCost alphabetLog
  have htail := mul_le_mul_of_nonneg_left (show (Fintype.card C:ℝ) ≤ Q by exact_mod_cast hQ)
    (show 0 ≤  s+1 by linarith)
  have hlog := mul_le_mul_of_nonneg_right htail alphabetLog_nonneg
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)
  dsimp only [alphabetLog] at hh
  linarith

open GirthAsymptotics TypedGraphs

/-- All patterns of the stated fixed bounds share one threshold. No offset,
chain length, bin, or word is fixed before this eventual quantifier. -/
theorem eventually_residual (K M Q : ℕ) : ∀ᶠ rep in atTop,
    ∀ (offset : Fin (Fintype.card E) → ℤ) (len m : C → ℕ),
      Fintype.card C ≤ Q → StageMass.totalLength len m ≤ K*(L (size rep):ℝ) →
      (L (size rep):ℝ) ≤ StageMass.totalLength len m → (∀ c,1 ≤ m c) →
      StageMass.residual (E := E) (chosenScale (Fintype.card E) (L (size rep)) offset) len m
        (letterError (Fintype.card E) (L (size rep)) offset) M Q
        (StageDenominator.error K Q rep) ≤ StageMass.totalLength len m/4800 := by
  have hL : Tendsto (fun rep => (L (size rep):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (L_tendsto.comp size_tendsto)
  have hr := ((GridUniform.rate_tendsto (Fintype.card E)).comp hL).const_mul
    (coefficient (Fintype.card E) K M Q)
  have he := (StageDenominator.error_ratio K Q).const_mul (M:ℝ)
  have ht := hr.add he
  simp only [mul_zero,add_zero] at ht
  have hevent := ht.eventually_lt_const (by norm_num : (0:ℝ)<1/4800)
  filter_upwards [hevent,hL.eventually (eventually_ge_atTop (1:ℝ))] with rep hrate hlen
  intro offset len m hQ hupper hlower hpos
  have h := residual_bound K M Q (L (size rep)) hlen offset len m hQ hupper hpos
    (StageDenominator.error K Q rep)
  have hrate' : coefficient (Fintype.card E) K M Q*GridUniform.rate (Fintype.card E)
      (L (size rep))+M*StageDenominator.error K Q rep/(L (size rep):ℝ) < 1/4800 := by
    simpa only [Function.comp_def,mul_div_assoc] using hrate
  have hb := (div_le_iff₀ (show (0:ℝ)<L (size rep) by linarith)).mp (h.trans hrate'.le)
  linarith
end TorsionFreeZeroDivisors.StageUniform
namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

def binRate (L : ℝ) : ℝ := (Real.log 257+Real.log L)/Real.sqrt L

theorem binRate_tendsto : Tendsto binRate atTop (𝓝 0) := by
  have hc : Tendsto (fun L : ℝ => Real.log 257/Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have he : (fun L : ℝ => Real.log L / L^(1/2:ℝ)) =
      (fun L : ℝ => Real.log L/Real.sqrt L) := by
    funext L
    rw [Real.sqrt_eq_rpow]
  rw [he] at hl
  unfold binRate
  simpa only [add_div,add_zero] using hc.add hl

theorem scale_le (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    chosenScale d L offset ≤ L := by
  have h := (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).2
  change chosenScale d L offset/L ≤ 1/(R d L:ℝ) at h
  have hR : (1:ℝ) ≤ R d L := by exact_mod_cast R_pos d hL
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hR
  norm_num only [div_one] at hi
  have hh := (div_le_iff₀ (show 0<L by linarith)).mp (h.trans hi)
  simpa only [one_mul] using hh

/-- A single common-grid bound for the logarithm of the number of all bin
profiles, without fixing any comparison offsets. -/
theorem bin_bound (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    Real.log (256*chosenScale d L offset+1)/chosenScale d L offset ≤ binRate L := by
  let s := chosenScale d L offset
  have hs : 0<s := chosenScale_pos d hL offset
  have hsl : s ≤ L := scale_le d hL offset
  have hlo := (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1
  change Real.sqrt L ≤ s at hlo
  have hL0 : 0<L := by linarith
  have hlog := Real.log_le_log (show 0<256*s+1 by positivity)
    (show 256*s+1 ≤ 257*L by linarith)
  rw [Real.log_mul (by norm_num : (257:ℝ)≠0) hL0.ne'] at hlog
  calc
    _ ≤ (Real.log 257+Real.log L)/s := div_le_div_of_nonneg_right hlog hs.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity [Real.log_nonneg hL])
      (Real.sqrt_pos.mpr hL0) hlo

end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] [Fintype E]

omit [Fintype C] in
theorem height_bounds (s : ℝ) (hs : 0 ≤ s) (len : C → ℕ) (i : Underlying s len) :
    s-1 ≤ (height s len i:ℝ) ∧ (height s len i:ℝ) ≤ s+1 := by
  have hl := card_lower ((i.2.val:ℝ)*s) (((i.2.val:ℝ)+1)*s)
  have hu := card_upper (lo := (i.2.val:ℝ)*s) (hi := ((i.2.val:ℝ)+1)*s) (by nlinarith)
  simp only [height,block,Int.cast_natCast]
  constructor <;> linarith

omit [Fintype E] in
/-- Feasible literal blocks obey BOTH entropy cutoffs and belong to the finite
profile family. This includes the empty block carrier. -/
theorem feasible_bounds (s : ℝ) (hs : 3003 ≤ s) (len m : C → ℕ)
    (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (W : (i : Underlying s len) → Fin (height s len i) → Letter)
    (hW : ActualStageLabels.Feasible s len m cmp d W) :
    d ∈ profiles s len ∧ ∀ i, (1/600:ℝ)*s/2 ≤ d i ∧ (d i:ℝ) ≤ 256*s := by
  have hh (i : Underlying s len) : 3002 ≤ height s len i ∧
      s+1200 ≤ 2*(height s len i:ℝ) ∧ (height s len i:ℝ) ≤ 2*s := by
    have hb := height_bounds s (by linarith) len i
    have hn : (3002:ℝ) ≤ height s len i := by linarith
    exact ⟨by exact_mod_cast hn,by linarith,by linarith⟩
  refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_),fun i => ?_⟩
  · exact mem_values (hh i).1 s (by linarith) (hh i).2.1 (hh i).2.2 (d i) (W i) (hW.1 i)
  · have h := bin_full_bounds (height s len i) (hh i).1 s (hh i).2.1 (hh i).2.2
      (d i) (W i) (hW.1 i)
    exact ⟨h.1,h.2.1⟩
end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

/-- An injective realization in a fixed sampled matching. These are actual
maps on vertices and ports; no random-event bound is part of the data. -/
structure Embedding (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
    (pin : PV → Option TV) (bar : T → T) (r : Matching (label outgoing) bar) where
  vertex : PV ↪ TV
  port : PD ↪ Dart outgoing
  origin_eq : ∀ d, origin outgoing (port d) = vertex (Γ.origin d)
  label_eq : ∀ d, label outgoing (port d) = plabel d
  reverse_eq : ∀ d, r.val (port d) = port (Γ.reverse d)
  pin_eq : ∀ v y, pin v = some y → vertex v = y

variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

include e in
omit [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T] in
theorem immersed : Function.Injective (fun d => (Γ.origin d,plabel d)) := by
  intro d f h
  apply e.port.injective
  apply Subtype.ext
  apply Prod.ext
  · change origin outgoing (e.port d) = origin outgoing (e.port f)
    rw [e.origin_eq,e.origin_eq]
    exact congrArg e.vertex (congrArg Prod.fst h)
  · change label outgoing (e.port d) = label outgoing (e.port f)
    rw [e.label_eq,e.label_eq]
    exact congrArg Prod.snd h

def vertexMap : VertexMap (StageRealization.allowed Γ plabel outgoing pin) :=
  ⟨e.vertex,e.vertex.injective,by
    intro v
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,e.pin_eq v⟩
    intro d hd
    have hp := (e.port d).property
    change label outgoing (e.port d) ∈ outgoing (origin outgoing (e.port d)) at hp
    simpa only [e.label_eq,e.origin_eq,hd] using hp⟩

omit [Fintype PV] [Fintype T] in
theorem dartMap_eq (d : PD) :
    dartMap Γ plabel outgoing _ (StageRealization.allowed_ports Γ plabel outgoing pin)
      (vertexMap e) d = e.port d := by
  apply Subtype.ext
  apply Prod.ext
  · exact (e.origin_eq d).symm
  · exact (e.label_eq d).symm

include e in
omit [Fintype T] in
/-- A literal embedding contributes at least one to the exact realization
count. The event direction is explicit rather than postulated. -/
theorem realizations_pos : 0 < StageRealization.realizations Γ plabel outgoing pin bar r := by
  apply Finset.card_pos.mpr
  refine ⟨vertexMap e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  intro d
  rw [dartMap_eq,dartMap_eq]
  exact e.reverse_eq d

variable {PV' PD' : Type*} [Fintype PV'] [Fintype PD']

/-- Graph isomorphisms, such as actual marked-chain subdivision, preserve
all event data, including the root pin and exact directed labels. -/
def pullback (Γ' : PortGraph PV' PD') (eV : PV' ≃ PV) (eD : PD' ≃ PD)
    (ho : ∀ d,eV (Γ'.origin d)=Γ.origin (eD d))
    (hr : ∀ d,eD (Γ'.reverse d)=Γ.reverse (eD d)) :
    Embedding Γ' (plabel ∘ eD) outgoing (pin ∘ eV) bar r where
  vertex := eV.toEmbedding.trans e.vertex
  port := eD.toEmbedding.trans e.port
  origin_eq d := by simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,ho] using e.origin_eq (eD d)
  label_eq d := e.label_eq (eD d)
  reverse_eq d := by simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,hr] using e.reverse_eq (eD d)
  pin_eq v y hy := e.pin_eq (eV v) y hy

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
variable {W : Type*}

/-- Every actual globally compatible embedding is contained in the event
counted by the two-side first moment. -/
theorem count_pos (A B : Side) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (r : A.Match × B.Match) (w : W) (hw : w∈X)
    (eA : RealizationTransport.Embedding (ChainSubdivision.graph A.len A.first A.last)
      (ChainRealization.label A.len (StageExpectation.readWord A.len (WA w))) A.outgoing
      (ChainRealization.pin A.len A.pin) Types.inverse r.1)
    (eB : RealizationTransport.Embedding (ChainSubdivision.graph B.len B.first B.last)
      (ChainRealization.label B.len (StageExpectation.readWord B.len (WB w))) B.outgoing
      (ChainRealization.pin B.len B.pin) Types.inverse r.2) :
    0<count A B X WA WB r := by
  have hm : w∈immersedLabels A B X WA WB :=
    Finset.mem_filter.mpr ⟨hw,RealizationTransport.immersed eA,RealizationTransport.immersed eB⟩
  have hp : 0<A.realizations (WA w) r.1*B.realizations (WB w) r.2 :=
    Nat.mul_pos (RealizationTransport.realizations_pos eA) (RealizationTransport.realizations_pos eB)
  apply hp.trans_le
  unfold count
  exact Finset.single_le_sum (f := fun w => A.realizations (WA w) r.1 * B.realizations (WB w) r.2)
    (fun _ _ => Nat.zero_le _) hm

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI
