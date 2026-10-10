import OAI.Analysis.DiamondDistortion.SignCube

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace DirectLayers

section
open SignCube Diamond
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I]
def signed (x y : X) (b : Bool) : X := if b then x-y else x+y
lemma signed_average (x y : X) : (1/2:ℝ) • (signed x y false+signed x y true)=x := by
  simp only [signed,Bool.false_eq_true,ite_false,ite_true]
  module
lemma signed_error {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (x y x' y' : X) (b : Bool) :
    ‖signed x y b-signed x' y' b‖ ≤ ‖x-x'‖+‖y-y'‖ := by
  cases b
  · change ‖x+y-(x'+y')‖ ≤ _
    rw [show x+y-(x'+y')=(x-x')+(y-y') by abel]
    exact norm_add_le _ _
  · change ‖x-y-(x'-y')‖ ≤ _
    rw [show x-y-(x'-y')=(x-x')-(y-y') by abel]
    exact norm_sub_le _ _
lemma signed_slope {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (j : ℕ) (b : Bool) :
    signed (slope (fun u => f (.inl u)) e) (deviation f e j) b=slope f (e,j,b) := by
  cases b
  · exact slope_plus_deviation f e j
  · exact slope_minus_deviation f e j
lemma deviation_bound {n : ℕ} (f : Vertex (n+1) → X) {L : ℝ}
    (hu : ∀ u v,‖f u-f v‖ ≤ L*distance (n+1) u v) (e : Edge n) (j : ℕ) :
    ‖deviation f e j‖ ≤ L := by
  apply norm_deviation_le (x := slope (fun u => f (.inl u)) e)
  · rw [slope_plus_deviation]; exact slope_upper f hu _
  · rw [slope_minus_deviation]; exact slope_upper f hu _

namespace Regular
variable {A : Midpoint.Heads I X} (hA : Regular A)
include hA
lemma signed_supported (H B : I) (hHB : H ≤ B) (x y : X) (hx : A.projection H x=x)
    (hy : A.projection B y=y) (b : Bool) : A.projection B (signed x y b)=signed x y b := by
  have hBx : A.projection B x=x := by rw [← hx,hA.nested_right _ _ hHB]
  cases b <;> simp [signed,map_add,map_sub,hBx,hy]
lemma signed_layer (H B : I) (hHB : H ≤ B) (x y : X) (hx : A.projection H x=x)
    (hy : A.projection B y=y) (b : Bool) :
    ‖A.projection B (signed x y b)-A.projection H (signed x y b)‖=‖y-A.projection H y‖ := by
  rw [hA.signed_supported H B hHB x y hx hy b]
  cases b
  · change ‖x+y-A.projection H (x+y)‖=_
    rw [map_add,hx,show x+y-(x+A.projection H y)=y-A.projection H y by abel]
  · change ‖x-y-A.projection H (x-y)‖=_
    rw [map_sub,hx,show x-y-(x-A.projection H y)=-(y-A.projection H y) by abel,norm_neg]
lemma projected_layer_lower (H B : I) (hHB : H ≤ B) (z : X) {r η : ℝ}
    (hr : r < ‖z-A.projection H z‖) (he : ‖z-A.projection B z‖ < η) :
    r-η < ‖A.projection B z-A.projection H (A.projection B z)‖ := by
  rw [hA.nested_left _ _ hHB]
  have hh := norm_sub_le (z-A.projection H z) (z-A.projection B z)
  rw [show (z-A.projection H z)-(z-A.projection B z)=A.projection B z-A.projection H z by abel] at hh
  have hh' := norm_sub_le (A.projection B z-A.projection H z) (A.projection B z-z)
  rw [show (A.projection B z-A.projection H z)-(A.projection B z-z)=z-A.projection H z by abel,
    norm_sub_rev (A.projection B z) z] at hh'
  linarith

lemma supported_selection (k : ℕ) (f : Vertex k → X) {s L η r q : ℝ}
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hu : ∀ u v,‖f u-f v‖ ≤ L*distance k u v)
    (hη : 0 < η) (hr : r < s) (hq : 0 ≤ q) (hqr : q ≤ r-η) :
    ∃ (T : Protocol X I k) (e : History k → Edge k),
      T.Martingale ∧ T.Nested ∧ T.Anchored ∧ T.CommonHeads ∧ T.Supported A.projection ∧
      (∀ u,‖T.last u-slope f (e u)‖ < ((k:ℝ)+1)*η) ∧
      (k:ℝ)*q^2 ≤ T.freshSum A.projection := by
  induction k with
  | zero =>
    obtain ⟨H⟩ := hA.nonempty
    obtain ⟨B,_,hB⟩ := hA.capture_one H (slope f ()) hη
    refine ⟨.initial (A.projection B (slope f ())) B,fun _ => (),trivial,trivial,trivial,trivial,
      A.idempotent B _,?_,?_⟩
    · intro u
      simpa only [Protocol.last,Nat.cast_zero,zero_add,one_mul,norm_sub_rev] using hB
    · simp only [Nat.cast_zero,zero_mul,Protocol.freshSum,le_refl]
  | succ n ih =>
    obtain ⟨T,e,hM,hN,hAn,hC,hS,hE,hF⟩ := ih (fun u => f (.inl u)) (old_lower f hl) (old_upper f hu)
    obtain ⟨H,hH⟩ := T.common_last hC
    have hsel (u : History n) : ∃ j,r < ‖deviation f (e u) j-A.projection H (deviation f (e u) j)‖ :=
      select_tail A H _ (deviation_bound f hu (e u))
        (fun i j hij => deviation_separated f hl (e u) hij) (by linarith)
    choose j hj using hsel
    let z : History n → X := fun u => deviation f (e u) (j u)
    obtain ⟨B,hHB,hB⟩ := hA.capture H z hη
    let v : History n → X := fun u => A.projection B (z u)
    let W : History (n+1) → X := fun u => signed (T.last u.1) (v u.1) u.2
    let T' : Protocol X I (n+1) := .extend T (fun _ => H) (fun _ => B) W
    have hHx (u : History n) : A.projection H (T.last u)=T.last u := by
      rw [← hH u]; exact T.supported_last A.projection hS u
    have hv (u : History n) : A.projection B (v u)=v u := A.idempotent B _
    refine ⟨T',fun u => (e u.1,j u.1,u.2),?_,?_,?_,?_,?_,?_,?_⟩
    · exact ⟨hM,fun u => (signed_average _ _).symm⟩
    · exact ⟨hN,fun u => ⟨(hH u).le,hHB⟩⟩
    · exact ⟨hAn,fun u => (hH u).symm⟩
    · exact ⟨hC,B,fun _ => rfl⟩
    · exact ⟨hS,fun u b => hA.signed_supported H B hHB _ _ (hHx u) (hv u) b⟩
    · intro u
      change ‖signed (T.last u.1) (v u.1) u.2-slope f (e u.1,j u.1,u.2)‖ < _
      rw [← signed_slope]
      have he := signed_error (T.last u.1) (v u.1)
        (slope (fun w => f (.inl w)) (e u.1)) (z u.1) u.2
      have hvz : ‖v u.1-z u.1‖ < η := by simpa only [v,norm_sub_rev] using hB u.1
      have he' := he.trans_lt (add_lt_add (hE u.1) hvz)
      exact he'.trans_eq (by push_cast; ring)
    · have hW (u : History (n+1)) : q^2 ≤ ‖A.projection B (W u)-A.projection H (W u)‖^2 := by
        rw [hA.signed_layer H B hHB _ _ (hHx u.1) (hv u.1) u.2]
        apply (sq_le_sq₀ hq (norm_nonneg _)).mpr
        exact hqr.trans (hA.projected_layer_lower H B hHB (z u.1) (hj u.1) (hB u.1)).le
      have he := mean_lower (n+1) hW
      change (n+1:ℕ)*q^2 ≤ T.freshSum A.projection+Protocol.childEnergy A.projection n (fun _ => H) (fun _ => B) W
      change q^2 ≤ Protocol.childEnergy A.projection n (fun _ => H) (fun _ => B) W at he
      push_cast
      nlinarith only [hF,he]
end Regular
end
section
open SignCube Diamond
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I]
variable (A : Midpoint.Heads I X) (hA : Regular A)

lemma approximate_bound {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I] {k : ℕ} (f : Vertex k → X) {L η C : ℝ}
    (hu : ∀ u v,‖f u-f v‖ ≤ L*distance k u v)
    (T : Protocol X I k) (e : History k → Edge k)
    (he : ∀ u,‖T.last u-slope f (e u)‖ < ((k:ℝ)+1)*η)
    (hC : L+((k:ℝ)+1)*η ≤ C) : ∀ u,‖T.last u‖ ≤ C := by
  intro u
  have hh := norm_sub_norm_le (T.last u) (slope f (e u))
  have hb := slope_upper f hu (e u)
  linarith [he u]

include hA

theorem predictable_graph (hin : PredictableInput A.projection 495) {D t : ℝ} (k : ℕ)
    (f : Vertex k → X) (hf : HasDistortion k f D t) : (k:ℝ)/4 ≤ 495*(D+1)^2 := by
  have hn := (normalized_distortion f hf).2.2
  let g := fun v => t⁻¹ • f v
  have hl : ∀ u v,(1:ℝ)*distance k u v ≤ ‖g u-g v‖ := fun u v => (hn u v).1
  have hu : ∀ u v,‖g u-g v‖ ≤ D*distance k u v := by simpa only [mul_one] using fun u v => (hn u v).2
  let η := 1/(8*((k:ℝ)+1))
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have heq : ((k:ℝ)+1)*η=1/8 := by dsimp [η]; field_simp
  have hηb : η ≤ 1/8 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨T,e,hM,hN,hAn,hC,hS,hE,hF⟩ := hA.supported_selection k g hl hu hη
    (by norm_num : (3/4:ℝ)<1) (by norm_num : (0:ℝ)≤1/2) (by linarith : (1/2:ℝ)≤3/4-η)
  have hb := approximate_bound g hu T e hE (C := D+1) (by rw [heq]; linarith)
  have hi := hin k T hM hN hAn hS (D+1) hb
  norm_num at hF
  nlinarith only [hF,hi]

theorem variation_graph (hin : PredictableInput A.projection 252) {D t : ℝ} (k : ℕ)
    (f : Vertex k → X) (hf : HasDistortion k f D t) : (k:ℝ)/(16*D^2) ≤ 1008 := by
  have hD : 0 < D := by linarith [hf.1]
  have hn := upper_one_normalization f hf
  let g := fun v => (D*t)⁻¹ • f v
  have hl : ∀ u v,D⁻¹*distance k u v ≤ ‖g u-g v‖ := fun u v => (hn u v).1
  have hu : ∀ u v,‖g u-g v‖ ≤ (1:ℝ)*distance k u v := by simpa only [one_mul] using fun u v => (hn u v).2
  let η := min (1/(4*D)) (1/((k:ℝ)+1))/2
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηD : η ≤ 1/(8*D) := by
    have hh := div_le_div_of_nonneg_right (min_le_left (1/(4*D)) (1/((k:ℝ)+1))) (by norm_num : (0:ℝ)≤2)
    exact hh.trans_eq (by field_simp; ring)
  have hηk : ((k:ℝ)+1)*η ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (min_le_right (1/(4*D)) (1/((k:ℝ)+1))) (by norm_num : (0:ℝ)≤2)) hk.le
    exact hh.trans_eq (by field_simp)
  have hr : 3/(4*D) < D⁻¹ := by rw [inv_eq_one_div]; apply (div_lt_div_iff₀ (by positivity) hD).mpr; nlinarith
  have hqr : 1/(4*D) ≤ 3/(4*D)-η := by
    have he : 3/(4*D)-1/(4*D)=4*(1/(8*D)) := by field_simp; ring
    have hp : 0 ≤ 1/(8*D) := by positivity
    linarith
  obtain ⟨T,e,hM,hN,hAn,hC,hS,hE,hF⟩ := hA.supported_selection k g hl hu hη hr
    (by positivity : (0:ℝ)≤1/(4*D)) hqr
  have hb := approximate_bound g hu T e hE (C := 2) (by linarith)
  have hi := hin k T hM hN hAn hS 2 hb
  have he : (k:ℝ)*(1/(4*D))^2=(k:ℝ)/(16*D^2) := by field_simp; ring
  rw [he] at hF
  norm_num at hi
  exact hF.trans hi

/-- The fresh-gap inequality telescopes for every supported predictable dyadic
    process, even when each increment contains a nonzero old-head part. -/
lemma gap_telescope (hin : GapInput A.projection) {k : ℕ} (T : Protocol X I k)
    (hM : T.Martingale) (hN : T.Nested) (hAn : T.Anchored) (hS : T.Supported A.projection) :
    T.freshSum A.projection ≤ 400*(T.terminalEnergy-T.initialEnergy) := by
  induction T with
  | initial x H => simp [Protocol.freshSum,Protocol.terminalEnergy,Protocol.last,Protocol.initialEnergy,mean]
  | @extend n T U B W ih =>
    have hprev := ih hM.1 hN.1 hAn.1 hS.1
    let y : History n → X := fun u => (1/2:ℝ) • (W (u,false)-W (u,true))
    have hx (u : History n) : A.projection (U u) (T.last u)=T.last u := by
      rw [hAn.2 u]; exact T.supported_last _ hS.1 u
    have hy (u : History n) : A.projection (B u) (y u)=y u := by
      dsimp [y]
      rw [map_smul,map_sub,hS.2 u false,hS.2 u true]
    have hw (u : History n) (b : Bool) : signed (T.last u) (y u) b=W (u,b) := by
      rw [hM.2 u]
      cases b <;> dsimp [signed,y] <;> module
    have hlayer (u : History n) (b : Bool) :
        ‖A.projection (B u) (W (u,b))-A.projection (U u) (W (u,b))‖=‖y u-A.projection (U u) (y u)‖ := by
      rw [← hw u b,hA.signed_layer _ _ (hN.2 u).2 _ _ (hx u) (hy u) b]
    have hgap (u : History n) : ‖y u-A.projection (U u) (y u)‖^2 ≤
        400*((‖W (u,false)‖^2+‖W (u,true)‖^2)/2-‖T.last u‖^2) := by
      have hh := hin (U u) (B u) (hN.2 u).2 (T.last u) (y u) (hx u) (hy u)
      rw [hy u] at hh
      have h0 := hw u false
      have h1 := hw u true
      change T.last u+y u=W (u,false) at h0
      change T.last u-y u=W (u,true) at h1
      rwa [h0,h1] at hh
    have heq : Protocol.childEnergy A.projection n U B W=mean n (fun u => ‖y u-A.projection (U u) (y u)‖^2) := by
      change mean n (fun u => (‖A.projection (B u) (W (u,false))-A.projection (U u) (W (u,false))‖^2+
        ‖A.projection (B u) (W (u,true))-A.projection (U u) (W (u,true))‖^2)/2)=_
      simp_rw [hlayer]
      congr 1
      funext u
      ring
    have hstep : Protocol.childEnergy A.projection n U B W ≤
        400*((Protocol.extend T U B W).terminalEnergy-T.terminalEnergy) := by
      rw [heq]
      have hh := mean_mono n hgap
      rw [mean_mul,mean_sub] at hh
      exact hh
    change T.freshSum A.projection+Protocol.childEnergy A.projection n U B W ≤
      400*((Protocol.extend T U B W).terminalEnergy-T.initialEnergy)
    linarith

theorem gap_graph (hin : GapInput A.projection) {D t γ : ℝ} (k : ℕ)
    (f : Vertex k → X) (hf : HasDistortion k f D t) (hγ : 0 < γ)
    (hγa : γ < (2/D)/8) (hγk : γ < 1/((k:ℝ)+1)) :
    ∃ T : Protocol X I k,T.Martingale ∧ T.Nested ∧ T.Anchored ∧ T.CommonHeads ∧ T.Supported A.projection ∧
      T.terminalEnergy ≤ 4 ∧ T.initialEnergy+(k:ℝ)*((2/D)/8)^2/400 ≤ T.terminalEnergy ∧
      (k:ℝ)*((2/D)/8)^2/400 ≤ T.initialEnergy+(k:ℝ)*((2/D)/8)^2/400 := by
  have hD : 0 < D := by linarith [hf.1]
  have hn := upper_one_normalization f hf
  let g := fun v => (D*t)⁻¹ • f v
  have hl : ∀ u v,D⁻¹*distance k u v ≤ ‖g u-g v‖ := fun u v => (hn u v).1
  have hu : ∀ u v,‖g u-g v‖ ≤ (1:ℝ)*distance k u v := by simpa only [one_mul] using fun u v => (hn u v).2
  have hr : (2/D)/4 < D⁻¹ := by rw [inv_eq_one_div]; field_simp; nlinarith
  have hqr : (2/D)/8 ≤ (2/D)/4-γ := by linarith
  obtain ⟨T,e,hM,hN,hAn,hC,hS,hE,hF⟩ := hA.supported_selection k g hl hu hγ hr
    (by positivity : (0:ℝ)≤(2/D)/8) hqr
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hγk' : ((k:ℝ)+1)*γ ≤ 1 := by
    have hh := (lt_div_iff₀ hk).mp hγk
    nlinarith
  have hb := approximate_bound g hu T e hE (C := 2) (by linarith)
  have htel := gap_telescope A hA hin T hM hN hAn hS
  refine ⟨T,hM,hN,hAn,hC,hS,?_,?_,?_⟩
  · simpa only [show (2:ℝ)^2=4 by norm_num] using T.terminalEnergy_bound (by norm_num) hb
  · linarith
  · linarith [T.initialEnergy_nonneg]
end

section
open SignCube Diamond
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I]
lemma norm_right_signed {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (x y : X) (b : Bool) : ‖y‖ ≤ ‖x‖+‖signed x y b‖ := by
  cases b
  · have hh := norm_sub_le (x+y) x
    rw [show x+y-x=y by abel] at hh
    change ‖y‖ ≤ ‖x‖+‖x+y‖
    linarith
  · have hh := norm_sub_le x (x-y)
    rw [show x-(x-y)=y by abel] at hh
    exact hh
lemma signed_tail (P : X →L[ℝ] X) (x y : X) (b : Bool) :
    signed x y b-P (signed x y b)=signed (x-P x) (y-P y) b := by
  cases b
  · dsimp [signed]; rw [map_add]; abel
  · dsimp [signed]; rw [map_sub]; abel

namespace Regular
variable {A : Midpoint.Heads I X} (hA : Regular A)
include hA
/-- Exact slopes, with a single common finite ancestral head on each level.
    Choosing the parent head slightly finer also ensures both child outcomes
    carry a fresh layer; this is valid for both adaptive and leakage inputs. -/
lemma true_selection (k : ℕ) (f : Vertex k → X) {s L η r q : ℝ}
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hu : ∀ u v,‖f u-f v‖ ≤ L*distance k u v)
    (hη : 0 < η) (hr : r < s) (hq : 0 ≤ q) (hqr : q ≤ r-2*η) :
    ∃ (T : Protocol X I k) (e : History k → Edge k),
      T.Martingale ∧ T.Nested ∧ T.Anchored ∧ T.CommonHeads ∧
      (∀ u,T.last u=slope f (e u)) ∧
      (∀ u,‖T.last u-A.projection (T.lastHead u) (T.last u)‖ < η) ∧
      (k:ℝ)*q^2 ≤ T.freshSum A.projection ∧ T.leakageSum A.projection ≤ (k:ℝ)*η^2 := by
  induction k with
  | zero =>
    obtain ⟨H⟩ := hA.nonempty
    obtain ⟨B,_,hB⟩ := hA.capture_one H (slope f ()) hη
    refine ⟨.initial (slope f ()) B,fun _ => (),trivial,trivial,trivial,trivial,
      fun _ => rfl,fun _ => hB,?_,?_⟩ <;>
      simp only [Nat.cast_zero,zero_mul,Protocol.freshSum,Protocol.leakageSum,le_refl]
  | succ n ih =>
    obtain ⟨T,e,hM,hN,hAn,hC,hE,hTail,hF,hLeak⟩ := ih (fun u => f (.inl u)) (old_lower f hl) (old_upper f hu)
    obtain ⟨H,hH⟩ := T.common_last hC
    have hsel (u : History n) : ∃ j,r < ‖deviation f (e u) j-A.projection H (deviation f (e u) j)‖ :=
      select_tail A H _ (deviation_bound f hu (e u))
        (fun i j hij => deviation_separated f hl (e u) hij) (by linarith)
    choose j hj using hsel
    let z : History n → X := fun u => deviation f (e u) (j u)
    let W : History (n+1) → X := fun u => signed (T.last u.1) (z u.1) u.2
    obtain ⟨B,hHB,hB⟩ := hA.capture H W hη
    let T' : Protocol X I (n+1) := .extend T (fun _ => H) (fun _ => B) W
    have hparent (u : History n) : ‖T.last u-A.projection H (T.last u)‖ < η := by
      rw [← hH u]; exact hTail u
    have hWtail (u : History (n+1)) : r-η < ‖W u-A.projection H (W u)‖ := by
      rw [signed_tail]
      have hh := norm_right_signed (T.last u.1-A.projection H (T.last u.1))
        (z u.1-A.projection H (z u.1)) u.2
      have hz := hj u.1
      change r < ‖z u.1-A.projection H (z u.1)‖ at hz
      linarith [hparent u.1]
    refine ⟨T',fun u => (e u.1,j u.1,u.2),?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact ⟨hM,fun u => (signed_average _ _).symm⟩
    · exact ⟨hN,fun u => ⟨(hH u).le,hHB⟩⟩
    · exact ⟨hAn,fun u => (hH u).symm⟩
    · exact ⟨hC,B,fun _ => rfl⟩
    · intro u
      change signed (T.last u.1) (z u.1) u.2=_
      rw [hE]
      exact signed_slope f (e u.1) (j u.1) u.2
    · exact hB
    · have hW (u : History (n+1)) : q^2 ≤ ‖A.projection B (W u)-A.projection H (W u)‖^2 := by
        have hh := hA.projected_layer_lower H B hHB (W u) (hWtail u) (hB u)
        rw [hA.nested_left H B hHB] at hh
        apply (sq_le_sq₀ hq (norm_nonneg _)).mpr
        linarith
      have he := mean_lower (n+1) hW
      change q^2 ≤ Protocol.childEnergy A.projection n (fun _ => H) (fun _ => B) W at he
      change (n+1:ℕ)*q^2 ≤ T.freshSum A.projection+Protocol.childEnergy A.projection n (fun _ => H) (fun _ => B) W
      push_cast
      nlinarith only [hF,he]
    · have hp (u : History n) : ‖A.projection B (T.last u)-A.projection H (T.last u)‖^2 ≤ η^2 := by
        exact (sq_le_sq₀ (norm_nonneg _) hη.le).mpr ((hA.layer_parent H B hHB _).trans (hparent u).le)
      have he := mean_upper n hp
      change Protocol.parentEnergy A.projection n (fun _ => H) (fun _ => B) T.last ≤ η^2 at he
      change T.leakageSum A.projection+Protocol.parentEnergy A.projection n (fun _ => H) (fun _ => B) T.last ≤ (n+1:ℕ)*η^2
      push_cast
      nlinarith only [hLeak,he]
end Regular
end

open SignCube Diamond
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I]
variable (A : Midpoint.Heads I X) (hA : Regular A)
include hA
lemma sign_constant_nonneg {C : ℝ} (hin : SignInput A.projection C) (x : X) (hx : 0 < ‖x‖) : 0 ≤ C := by
  obtain ⟨H⟩ := hA.nonempty
  have hh := hin 0 (.initial x H) trivial trivial
  simp only [Protocol.freshSum,Protocol.leakageSum,Protocol.terminalEnergy,mean,Protocol.last,add_zero] at hh
  have hp := sq_pos_of_pos hx
  by_contra! hn
  exact (mul_neg_of_neg_of_pos hn hp).not_ge hh

omit hA in
lemma dyadic_budget (k : ℕ) : (k:ℝ)*((2:ℝ)^k)⁻¹^2 ≤ 1 := by
  have hp : (k:ℝ)+1 ≤ (4:ℝ)^k := by
    induction k with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      push_cast
      have hn := Nat.cast_nonneg (α := ℝ) n
      nlinarith
  have he : ((2:ℝ)^k)^2=(4:ℝ)^k := by
    rw [← pow_mul,mul_comm k 2,pow_mul]
    norm_num
  have hh : (k:ℝ) ≤ ((2:ℝ)^k)^2 := by rw [he]; linarith
  have hd : 0 < ((2:ℝ)^k)^2 := by positivity
  have hb := mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hd.le)
  rw [mul_inv_cancel₀ hd.ne'] at hb
  simpa only [inv_pow] using hb

theorem adaptive_graph {C : ℝ} (hin : SignInput A.projection C) {D t : ℝ} (k : ℕ)
    (f : Vertex k → X) (hf : HasDistortion k f D t) :
    (k:ℝ)/16 ≤ C*(D^2+(k:ℝ)*((2:ℝ)^k)⁻¹^2) ∧
      C*(D^2+(k:ℝ)*((2:ℝ)^k)⁻¹^2) ≤ C*(D^2+1) := by
  have hn := (normalized_distortion f hf).2.2
  let g := fun v => t⁻¹ • f v
  have hl : ∀ u v,(1:ℝ)*distance k u v ≤ ‖g u-g v‖ := fun u v => (hn u v).1
  have hu : ∀ u v,‖g u-g v‖ ≤ D*distance k u v := by simpa only [mul_one] using fun u v => (hn u v).2
  have hC : 0 ≤ C := sign_constant_nonneg A hA hin (slope g (baseEdge k))
    (lt_of_lt_of_le (by norm_num) (slope_lower g hl _))
  let η := min (((2:ℝ)^k)⁻¹) (1/8)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/8 := min_le_right _ _
  have hη2 : η ≤ ((2:ℝ)^k)⁻¹ := min_le_left _ _
  obtain ⟨T,e,hM,hN,hAn,hCommon,hE,hTail,hF,hLeak⟩ := hA.true_selection k g hl hu hη
    (by norm_num : (3/4:ℝ)<1) (by norm_num : (0:ℝ)≤1/4) (by linarith : (1/4:ℝ)≤3/4-2*η)
  have ht : T.terminalEnergy ≤ D^2 := T.terminalEnergy_bound (by linarith [hf.1])
    (fun u => by rw [hE]; exact slope_upper g hu _)
  have hηsq : η^2 ≤ (((2:ℝ)^k)⁻¹)^2 := (sq_le_sq₀ hη.le (by positivity)).mpr hη2
  have hlk := hLeak.trans (mul_le_mul_of_nonneg_left hηsq (Nat.cast_nonneg k))
  have hi := (hin k T hM hN).trans (mul_le_mul_of_nonneg_left (add_le_add ht hlk) hC)
  constructor
  · norm_num at hF
    nlinarith only [hF,hi]
  · exact mul_le_mul_of_nonneg_left (add_le_add (le_refl (D^2)) (dyadic_budget k)) hC

def leakageTolerance (k : ℕ) : ℝ := min (1/8) (1/Real.sqrt (k:ℝ))
omit hA in
lemma leakage_tolerance_properties {k : ℕ} (hk : 1 ≤ k) :
    0 < leakageTolerance k ∧ leakageTolerance k ≤ 1/8 ∧ (k:ℝ)*(leakageTolerance k)^2 ≤ 1 := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hk0
  have hε : 0 < leakageTolerance k := by unfold leakageTolerance; positivity
  refine ⟨hε,min_le_left _ _,?_⟩
  have hh : (leakageTolerance k)^2 ≤ (1/Real.sqrt (k:ℝ))^2 :=
    (sq_le_sq₀ hε.le (by positivity)).mpr (min_le_right _ _)
  calc
    _ ≤ (k:ℝ)*(1/Real.sqrt (k:ℝ))^2 := mul_le_mul_of_nonneg_left hh hk0.le
    _ = 1 := by rw [div_pow,one_pow,Real.sq_sqrt hk0.le]; field_simp

theorem leakage_graph (hin : LeakageInput A.projection) {D t : ℝ} (k : ℕ) (hk : 1 ≤ k)
    (f : Vertex k → X) (hf : HasDistortion k f D t) :
    (k:ℝ)/8 ≤ 1024*(D^2+(k:ℝ)*(leakageTolerance k)^2) ∧
      1024*(D^2+(k:ℝ)*(leakageTolerance k)^2) ≤ 1024*(D^2+1) := by
  have hn := (normalized_distortion f hf).2.2
  let g := fun v => t⁻¹ • f v
  have hl : ∀ u v,(1:ℝ)*distance k u v ≤ ‖g u-g v‖ := fun u v => (hn u v).1
  have hu : ∀ u v,‖g u-g v‖ ≤ D*distance k u v := by simpa only [mul_one] using fun u v => (hn u v).2
  obtain ⟨hη,hηb,hbudget⟩ := leakage_tolerance_properties hk
  obtain ⟨T,e,hM,hN,hAn,hCommon,hE,hTail,hF,hLeak⟩ := hA.true_selection k g hl hu hη
    (by norm_num : (3/4:ℝ)<1) (by norm_num : (0:ℝ)≤1/2) (by linarith : (1/2:ℝ)≤3/4-2*leakageTolerance k)
  have ht : T.terminalEnergy ≤ D^2 := T.terminalEnergy_bound (by linarith [hf.1])
    (fun u => by rw [hE]; exact slope_upper g hu _)
  have hi := hin k T hM hN hAn hCommon
  constructor
  · norm_num at hF
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  · linarith
end DirectLayers

end DiamondDistortion

end

end OAI
