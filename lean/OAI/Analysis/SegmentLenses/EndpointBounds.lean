import OAI.Analysis.SegmentLenses.Separated

namespace OAI

/-!
# Endpoint bounds, clipping, and gate coordinates
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

section EndpointGlobal
open scoped Classical
variable {V ΩP ΩM : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]
  [Fintype ΩP] [Fintype ΩM]




theorem endpoint_laws_on_gates {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (_hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) {d : ℝ} (hd : 0 ≤ d) (_hd1 : d < 1)
    (hxn : 1 - d ≤ ‖x‖) (_hplus : ‖x + y‖ ≤ 1) (_hminus : ‖x - y‖ ≤ 1)
    (p : Test V) (hpH : p.coeff.support ⊆ H) (hp : ‖p‖ = 1) (hxp : x (p : Primal V) = ‖x‖)
    (μP : FiniteLaw ΩP) (μM : FiniteLaw ΩM)
    (AP : ΩP → Representation V) (AM : ΩM → Representation V)
    (hAP : ∀ ω, (AP ω).energy ≤ 1) (hAM : ∀ ω, (AM ω).energy ≤ 1)
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g)
    (hmeanP : μP.expect (fun ω => (AP ω).value) = head K (x + y))
    (hmeanM : μM.expect (fun ω => (AM ω).value) = head K (x - y)) :
    let mP := fun g : G => μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|)
    let mM := fun g : G => μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|)
    let m := fun g => (mP g + mM g) / 2
    (lawSlack μP AP p + lawError μP AP p ≤ 4 * d) ∧
    (lawSlack μM AM p + lawError μM AM p ≤ 4 * d) ∧
    μP.mean (fun ω => ‖(AP ω).value - ((AP ω).family.replacement p.coeff).value‖) ≤ 2 * Real.sqrt d ∧
    μM.mean (fun ω => ‖(AM ω).value - ((AM ω).family.replacement p.coeff).value‖) ≤ 2 * Real.sqrt d ∧
    (∀ g, 0 ≤ mP g ∧ 0 ≤ mM g ∧ mP g ≤ 2 * m g ∧ mM g ≤ 2 * m g) ∧
    Real.sqrt (∑ g, m g ^ 2) ≤ Real.sqrt (6 * d) := by
  classical
  dsimp only
  let μ := μP.pooled μM
  let A := Sum.elim AP AM
  have hA : ∀ ω, (A ω).energy ≤ 1 := by intro ω; cases ω with | inl ω => exact hAP ω | inr ω => exact hAM ω
  have hmean : μ.expect (fun ω => (A ω).value) = x := by
    have he : (fun ω => (A ω).value) = Sum.elim (fun ω => (AP ω).value) (fun ω => (AM ω).value) := by
      funext ω; cases ω <;> rfl
    rw [he, μP.pooled_expect μM, hmeanP, hmeanM]
    change (1/2 : ℝ) • headLinear K (x + y) + (1/2 : ℝ) • headLinear K (x - y) = x
    rw [map_add, map_sub, headLinear_apply, head_eq_of_subset hHK x hx]
    module
  have hdef : lawDeficit μ A p = 1 - ‖x‖ := by rw [lawDeficit, hmean, hxp]
  have hdefsum : lawDeficit μP AP p + lawDeficit μM AM p = 2 * (1 - ‖x‖) := by
    have he : μ.mean (fun ω => (A ω).value (p : Primal V)) =
        (μP.mean (fun ω => (AP ω).value (p : Primal V)) +
          μM.mean (fun ω => (AM ω).value (p : Primal V))) / 2 := by
      have hf : (fun ω => (A ω).value (p : Primal V)) =
          Sum.elim (fun ω => (AP ω).value (p : Primal V)) (fun ω => (AM ω).value (p : Primal V)) := by
        funext ω; cases ω <;> rfl
      rw [hf]
      exact μP.pooled_mean μM _ _
    have he' : μ.mean (fun ω => (A ω).value (p : Primal V)) = ‖x‖ := by
      rw [← μ.expect_apply, hmean, hxp]
    simp only [lawDeficit, FiniteLaw.expect_apply]
    linarith
  have hdP := lawDeficit_nonneg μP AP hAP p hp.le
  have hdM := lawDeficit_nonneg μM AM hAM p hp.le
  have hbP : lawDeficit μP AP p ≤ 2 * d := by linarith
  have hbM : lawDeficit μM AM p ≤ 2 * d := by linarith
  have hrootP : Real.sqrt (2 * lawDeficit μP AP p) ≤ 2 * Real.sqrt d := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hd]
  have hrootM : Real.sqrt (2 * lawDeficit μM AM p) ≤ 2 * Real.sqrt d := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hd]
  refine ⟨?_, ?_, (mean_error_norm_le μP AP hAP p hp.le).trans hrootP,
    (mean_error_norm_le μM AM hAM p hp.le).trans hrootM, ?_, ?_⟩
  · have h := (unit_law_budget μP AP hAP p hp.le).2.2
    linarith
  · have h := (unit_law_budget μM AM hAM p hp.le).2.2
    linarith
  · intro g
    have hpos := μP.mean_nonneg (fun ω => abs_nonneg ((AP ω).family.boundary p.coeff g.val))
    have hneg := μM.mean_nonneg (fun ω => abs_nonneg ((AM ω).family.boundary p.coeff g.val))
    exact ⟨hpos, hneg, by linarith, by linarith⟩
  · apply Real.sqrt_le_sqrt
    have h := law_absolute_mass_bound hH (G)
      hG μ A hA p hp.le hpH
    have ht : tail H x = 0 := by simp only [tail, hx, sub_self]
    rw [hmean, ht, norm_zero, zero_add, hdef] at h
    have hδ : 0 ≤ 1 - ‖x‖ := hdef ▸ lawDeficit_nonneg μ A hA p hp.le
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hδ)] at h
    have he : ∀ g : G, μ.mean (fun ω => |(A ω).family.boundary p.coeff g.val|) =
        (μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|) +
          μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|)) / 2 := by
      intro g
      have hf : (fun ω => |(A ω).family.boundary p.coeff g.val|) =
          Sum.elim (fun ω => |(AP ω).family.boundary p.coeff g.val|)
            (fun ω => |(AM ω).family.boundary p.coeff g.val|) := by
        funext ω; cases ω <;> rfl
      rw [hf]
      exact μP.pooled_mean μM _ _
    simp_rw [he] at h
    linarith

end EndpointGlobal


section LawWrappers
open scoped Classical
variable {V Ω : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V] [Fintype Ω]



def lawSupport (A : Ω → Representation V) : Finset V :=
  Finset.univ.biUnion (fun ω => (A ω).family.sets.biUnion id)

theorem subset_lawSupport (A : Ω → Representation V) (ω : Ω) (S : Finset V)
    (hS : S ∈ (A ω).family.sets) : S ⊆ lawSupport A := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨ω, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨S,hS,hv⟩⟩


theorem bounded_multiplier {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (A : Ω → Representation V) (hA : ∀ ω, (A ω).energy ≤ 1)
    (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (p : Test V) (hp : ‖p‖ ≤ 1) (hpH : p.coeff.support ⊆ H) :
    ‖tail H (μ.expect (fun ω => σ ω • (A ω).value))‖ ≤
      Real.sqrt ((‖tail H (μ.expect (fun ω => (A ω).value))‖ + Real.sqrt (2 * lawDeficit μ A p)) ^ 2 +
        4 * lawDeficit μ A p) + Real.sqrt (2 * lawDeficit μ A p) ∧
    Real.sqrt ((‖tail H (μ.expect (fun ω => (A ω).value))‖ + Real.sqrt (2 * lawDeficit μ A p)) ^ 2 +
        4 * lawDeficit μ A p) + Real.sqrt (2 * lawDeficit μ A p) ≤
      ‖tail H (μ.expect (fun ω => (A ω).value))‖ + (2+2*Real.sqrt 2)*Real.sqrt (lawDeficit μ A p) :=
  ⟨represented_bounded_multiplier hH μ A hA (subset_lawSupport A) σ hσ p hp hpH,
    stable_radical_linear (norm_nonneg _) (lawDeficit_nonneg μ A hA p hp)⟩

end LawWrappers

namespace FiniteLaw

def equalPair : FiniteLaw Bool where
  weight _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num

@[simp] theorem equalPair_expect {E : Type*} [AddCommMonoid E] [Module ℝ E] (z : Bool → E) :
    equalPair.expect z = (1/2:ℝ) • z false + (1/2:ℝ) • z true := by
  simp only [expect, equalPair, Fintype.sum_bool, add_comm]

end FiniteLaw

section EqualEndpointStability
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]


theorem nonzero_midpoint_bound {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (zp zm : FullDual V) (hpz : ‖zp‖ ≤ 1) (hmz : ‖zm‖ ≤ 1)
    (p : Test V) (hp : ‖p‖ ≤ 1) (hpH : p.coeff.support ⊆ H) :
    let x := (1/2:ℝ) • zp + (1/2:ℝ) • zm
    let δ := 1 - x (p : Primal V)
    ∀ z ∈ ({zp,zm} : Set (FullDual V)),
      ‖tail H z‖ ≤ 2 * Real.sqrt ((‖tail H x‖ + Real.sqrt (2*δ))^2 + 4*δ) + 2*Real.sqrt δ := by
  classical
  dsimp only
  let Z : Bool → FullDual V := fun b => if b then zm else zp
  have hZ : ∀ b, ‖Z b‖ ≤ 1 := by intro b; cases b <;> assumption
  have hw : ∀ b, 0 < FiniteLaw.equalPair.weight b := by intro b; norm_num [FiniteLaw.equalPair]
  have he : FiniteLaw.equalPair.expect Z = (1/2:ℝ)•zp+(1/2:ℝ)•zm := by
    rw [FiniteLaw.equalPair_expect]; rfl
  have hd := weighted_deficits (H := H) FiniteLaw.equalPair hw Z hZ p hp
  have hδ : 0 ≤ 1 - (FiniteLaw.equalPair.expect Z) (p : Primal V) := by
    rw [hd.2.1]
    exact FiniteLaw.equalPair.mean_nonneg hd.1
  have hb : ∀ b, ‖tail H (Z b)‖ ≤
      2 * Real.sqrt ((‖tail H (FiniteLaw.equalPair.expect Z)‖ +
        Real.sqrt (2*(1-(FiniteLaw.equalPair.expect Z) (p : Primal V))))^2 +
          4*(1-(FiniteLaw.equalPair.expect Z) (p : Primal V))) +
            2*Real.sqrt (1-(FiniteLaw.equalPair.expect Z) (p : Primal V)) := by
    intro b
    have h := weighted_tail_bound hH FiniteLaw.equalPair hw Z hZ p hp hpH b
    have hi := hd.2.2 b
    have hweight : FiniteLaw.equalPair.weight b = (1/2:ℝ) := rfl
    rw [hweight] at hi h
    norm_num only [inv_div, inv_one, div_one] at h
    rw [div_div_eq_mul_div, div_one] at hi
    have hroot : Real.sqrt (2*(1-Z b (p : Primal V))) ≤
        2*Real.sqrt (1-(FiniteLaw.equalPair.expect Z) (p : Primal V)) := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt hδ]
    exact h.trans (add_le_add le_rfl hroot)
  rw [he] at hb
  intro z hz
  rcases hz with rfl | rfl
  · exact hb false
  · exact hb true

end EqualEndpointStability


section SubtypeL2
open scoped ENNReal
variable {V : Type*} [decidableEqV : DecidableEq V]



theorem subtype_l2_bound (P : V → Prop) (a : V → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ G : Finset V, (∀ g ∈ G, P g) → Real.sqrt (∑ g : G, a g.val ^ 2) ≤ C) :
    ∃ m : lp (fun _ : {g // P g} => ℝ) 2, (∀ g, m g = a g.val) ∧ ‖m‖ ≤ C := by
  have _ := decidableEqV
  classical
  have hs : ∀ s : Finset {g // P g}, ∑ g ∈ s, ‖a g.val‖^2 ≤ C^2 := by
    intro s
    let e : {g // P g} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    let G := s.map e
    have hG : ∀ g ∈ G, P g := by
      intro g hg
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hg
      exact v.property
    have hb := h G hG
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hC).mpr hb
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hsq
    rw [Finset.sum_coe_sort G (fun g : V => a g ^ 2)] at hsq
    simpa only [G, Finset.sum_map, e, Function.Embedding.coeFn_mk, Real.norm_eq_abs, sq_abs] using hsq
  let m : lp (fun _ : {g // P g} => ℝ) 2 := ⟨fun g => a g.val,
    memℓp_gen' (C := C^2) (fun s => by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs s)⟩
  refine ⟨m, fun _ => rfl, ?_⟩
  apply lp.norm_le_of_forall_sum_le (by norm_num) hC
  intro s
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, m] using hs s

end SubtypeL2

section EndpointL2
open scoped Classical
variable {V ΩP ΩM : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]
  [Fintype ΩP] [Fintype ΩM]



theorem endpoint_laws_global {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hxn : 1 - d ≤ ‖x‖) (hplus : ‖x+y‖ ≤ 1) (hminus : ‖x-y‖ ≤ 1)
    (p : Test V) (hpH : p.coeff.support ⊆ H) (hp : ‖p‖ = 1) (hxp : x (p : Primal V) = ‖x‖)
    (μP : FiniteLaw ΩP) (μM : FiniteLaw ΩM)
    (AP : ΩP → Representation V) (AM : ΩM → Representation V)
    (hAP : ∀ ω, (AP ω).energy ≤ 1) (hAM : ∀ ω, (AM ω).energy ≤ 1)
    (hmeanP : μP.expect (fun ω => (AP ω).value) = head K (x+y))
    (hmeanM : μM.expect (fun ω => (AM ω).value) = head K (x-y)) :
    (lawSlack μP AP p + lawError μP AP p ≤ 4*d) ∧
    (lawSlack μM AM p + lawError μM AM p ≤ 4*d) ∧
    μP.mean (fun ω => ‖(AP ω).value - ((AP ω).family.replacement p.coeff).value‖) ≤ 2*Real.sqrt d ∧
    μM.mean (fun ω => ‖(AM ω).value - ((AM ω).family.replacement p.coeff).value‖) ≤ 2*Real.sqrt d ∧
    ∃ m : lp (fun _ : {g // Gate H g} => ℝ) 2,
      (∀ g, m g = (μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|) +
        μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|))/2) ∧
      ‖m‖ ≤ Real.sqrt (6*d) ∧
      (∀ g, 0 ≤ μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|) ∧
        0 ≤ μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|) ∧
        μP.mean (fun ω => |(AP ω).family.boundary p.coeff g.val|) ≤ 2*m g ∧
        μM.mean (fun ω => |(AM ω).family.boundary p.coeff g.val|) ≤ 2*m g) := by
  classical
  have h0 := endpoint_laws_on_gates hH hK hHK x y hx hd hd1 hxn hplus hminus p hpH hp hxp
    μP μM AP AM hAP hAM ∅ (by simp) hmeanP hmeanM
  refine ⟨h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,?_⟩
  obtain ⟨m,hm,hmn⟩ := subtype_l2_bound (Gate H)
    (fun g => (μP.mean (fun ω => |(AP ω).family.boundary p.coeff g|) +
      μM.mean (fun ω => |(AM ω).family.boundary p.coeff g|))/2)
    (Real.sqrt_nonneg (6*d)) (fun G hG =>
      (endpoint_laws_on_gates hH hK hHK x y hx hd hd1 hxn hplus hminus p hpH hp hxp
        μP μM AP AM hAP hAM G hG hmeanP hmeanM).2.2.2.2.2)
  refine ⟨m,hm,hmn,?_⟩
  intro g
  rw [hm]
  have hp0 := μP.mean_nonneg (fun ω => abs_nonneg ((AP ω).family.boundary p.coeff g.val))
  have hm0 := μM.mean_nonneg (fun ω => abs_nonneg ((AM ω).family.boundary p.coeff g.val))
  exact ⟨hp0,hm0,by linarith,by linarith⟩

end EndpointL2

section GateCoordinateL2
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

theorem gate_coordinate_l2 (H : Finset V) (z : FullDual V) :
    ∃ m : lp (fun _ : {g // Gate H g} => ℝ) 2,
      (∀ g, m g = z (unitVector g.val)) ∧ ‖m‖ ≤ ‖z‖ := by
  apply subtype_l2_bound (Gate H) (fun g => z (unitVector g)) (norm_nonneg z)
  intro G hG
  apply (Real.sqrt_le_iff).mpr
  exact ⟨norm_nonneg z, gate_coordinate_square_sum G hG z⟩

end GateCoordinateL2




end SegmentLenses

end

end OAI
