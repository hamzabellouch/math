import OAI.Analysis.DiamondDistortion.RecursiveBounds

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace SignCube
abbrev History : ℕ → Type
  | 0 => Unit
  | n+1 => History n × Bool
instance (n : ℕ) : Fintype (History n) := by induction n with | zero => infer_instance | succ n ih => exact inferInstance
instance (n : ℕ) : Nonempty (History n) := by induction n with | zero => infer_instance | succ n ih => exact inferInstance
lemma history_card (n : ℕ) : Fintype.card (History n)=2^n := by
  induction n with
  | zero => rfl
  | succ n ih => change Fintype.card (History n × Bool)=_; rw [Fintype.card_prod,ih,Fintype.card_bool,pow_succ]

/-- Expectation for the uniform sign probability, written as iterated fair averages. -/
def mean : (n : ℕ) → (History n → ℝ) → ℝ
  | 0,f => f ()
  | n+1,f => mean n (fun h => (f (h,false)+f (h,true))/2)
@[simp] lemma mean_zero (n : ℕ) : mean n (fun _ => 0)=0 := by
  induction n with | zero => rfl | succ n ih => simpa only [mean,zero_add,zero_div] using ih
@[simp] lemma mean_const (n : ℕ) (c : ℝ) : mean n (fun _ => c)=c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [mean,show (c+c)/2=c by ring] using ih
lemma mean_mono (n : ℕ) {f g : History n → ℝ} (hfg : ∀ h,f h ≤ g h) : mean n f ≤ mean n g := by
  induction n with
  | zero => exact hfg ()
  | succ n ih => exact ih (fun h => by change (f (h,false)+f (h,true))/2 ≤ _; linarith [hfg (h,false),hfg (h,true)])
lemma mean_nonneg (n : ℕ) {f : History n → ℝ} (hf : ∀ h,0 ≤ f h) : 0 ≤ mean n f := by
  simpa only [mean_zero] using mean_mono n hf
lemma mean_lower (n : ℕ) {f : History n → ℝ} {a : ℝ} (hf : ∀ h,a ≤ f h) : a ≤ mean n f := by
  simpa only [mean_const] using mean_mono n hf
lemma mean_upper (n : ℕ) {f : History n → ℝ} {a : ℝ} (hf : ∀ h,f h ≤ a) : mean n f ≤ a := by
  simpa only [mean_const] using mean_mono n hf
lemma mean_add (n : ℕ) (f g : History n → ℝ) : mean n (fun h => f h+g h)=mean n f+mean n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change mean n (fun h => (f (h,false)+g (h,false)+(f (h,true)+g (h,true)))/2)=_
    simp_rw [show ∀ a b c d : ℝ,(a+b+(c+d))/2=(a+c)/2+(b+d)/2 by intros; ring]
    exact ih _ _
lemma mean_mul (n : ℕ) (c : ℝ) (f : History n → ℝ) : mean n (fun h => c*f h)=c*mean n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change mean n (fun h => (c*f (h,false)+c*f (h,true))/2)=_
    simp_rw [show ∀ a b : ℝ,(c*a+c*b)/2=c*((a+b)/2) by intros; ring]
    exact ih _
lemma mean_sub (n : ℕ) (f g : History n → ℝ) : mean n (fun h => f h-g h)=mean n f-mean n g := by
  have he (h : History n) : f h-g h=f h+(-1)*g h := by ring
  simp_rw [he]
  rw [mean_add,mean_mul]
  ring
lemma mean_last (n : ℕ) (f : History n → ℝ) : mean (n+1) (fun h => f h.1)=mean n f := by
  simp only [mean,show ∀ a : ℝ,(a+a)/2=a by intro; ring]
lemma mean_uniform (n : ℕ) (f : History n → ℝ) :
    mean n f=(∑ h,f h)/(Fintype.card (History n):ℝ) := by
  induction n with
  | zero => simp [mean]
  | succ n ih =>
    change mean n (fun h => (f (h,false)+f (h,true))/2)=_
    rw [ih,← Finset.sum_div,Finset.sum_add_distrib]
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,Finset.sum_add_distrib]
    ring

inductive Protocol (X : Type u) (I : Type v) : ℕ → Type (max u v)
  | initial (x : X) (H : I) : Protocol X I 0
  | extend {n : ℕ} (prev : Protocol X I n) (A B : History n → I)
      (next : History (n+1) → X) : Protocol X I (n+1)
namespace Protocol
variable {X I : Type*}
def last : {n : ℕ} → Protocol X I n → History n → X
  | 0,.initial x _,_ => x
  | _+1,.extend _ _ _ W,h => W h
def lastHead : {n : ℕ} → Protocol X I n → History n → I
  | 0,.initial _ H,_ => H
  | _+1,.extend _ _ B _,h => B h.1

variable [NormedAddCommGroup X] [NormedSpace ℝ X]
/-- Fair one-step conditional expectations. Iterating gives W_i=E(W_m|F_i). -/
def Martingale : {n : ℕ} → Protocol X I n → Prop
  | 0,.initial _ _ => True
  | _+1,.extend T _ _ W => Martingale T ∧ ∀ h,T.last h=(1/2:ℝ) • (W (h,false)+W (h,true))
variable [Preorder I]
def Nested : {n : ℕ} → Protocol X I n → Prop
  | 0,.initial _ _ => True
  | _+1,.extend T A B _ => Nested T ∧ ∀ h,T.lastHead h ≤ A h ∧ A h ≤ B h
/-- Each layer is between consecutive support heads, not separated by a new
    unrecorded head. This is imposed only for the inputs that require it. -/
def Anchored : {n : ℕ} → Protocol X I n → Prop
  | 0,.initial _ _ => True
  | _+1,.extend T A _ _ => Anchored T ∧ ∀ h,A h=T.lastHead h
/-- Fixed across each level (stronger than predictability); required only by the
    deterministic leakage input. -/
def CommonHeads : {n : ℕ} → Protocol X I n → Prop
  | 0,.initial _ _ => True
  | _+1,.extend T _ B _ => CommonHeads T ∧ ∃ H,∀ h,B h=H

def Supported (P : I → X →L[ℝ] X) : {n : ℕ} → Protocol X I n → Prop
  | 0,.initial x H => P H x=x
  | _+1,.extend T _ B W => Supported P T ∧ ∀ h b,P (B h) (W (h,b))=W (h,b)

def childEnergy (P : I → X →L[ℝ] X) (n : ℕ) (A B : History n → I) (W : History (n+1) → X) : ℝ :=
  mean (n+1) (fun h => ‖P (B h.1) (W h)-P (A h.1) (W h)‖^2)
def parentEnergy (P : I → X →L[ℝ] X) (n : ℕ) (A B : History n → I) (W : History n → X) : ℝ :=
  mean n (fun h => ‖P (B h) (W h)-P (A h) (W h)‖^2)
def freshSum (P : I → X →L[ℝ] X) : {n : ℕ} → Protocol X I n → ℝ
  | 0,.initial _ _ => 0
  | n+1,.extend T A B W => freshSum P T+childEnergy P n A B W
def leakageSum (P : I → X →L[ℝ] X) : {n : ℕ} → Protocol X I n → ℝ
  | 0,.initial _ _ => 0
  | n+1,.extend T A B _ => leakageSum P T+parentEnergy P n A B T.last

def terminalEnergy {n : ℕ} (T : Protocol X I n) : ℝ := mean n (fun h => ‖T.last h‖^2)
lemma terminalEnergy_nonneg {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I] {n : ℕ} (T : Protocol X I n) : 0 ≤ T.terminalEnergy :=
  mean_nonneg _ (fun _ => sq_nonneg _)
lemma terminalEnergy_bound {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I] {n : ℕ} (T : Protocol X I n) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ u,‖T.last u‖ ≤ D) : T.terminalEnergy ≤ D^2 :=
  mean_upper _ (fun u => (sq_le_sq₀ (norm_nonneg _) hD).mpr (h u))
lemma freshSum_nonneg {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I] (P : I → X →L[ℝ] X) {n : ℕ} (T : Protocol X I n) : 0 ≤ T.freshSum P := by
  induction T with
  | initial x H => exact le_rfl
  | @extend n T A B W ih => exact add_nonneg ih (mean_nonneg _ (fun _ => sq_nonneg _))
lemma leakageSum_nonneg {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I] (P : I → X →L[ℝ] X) {n : ℕ} (T : Protocol X I n) : 0 ≤ T.leakageSum P := by
  induction T with
  | initial x H => exact le_rfl
  | @extend n T A B W ih => exact add_nonneg ih (mean_nonneg _ (fun _ => sq_nonneg _))
end Protocol
end SignCube

namespace DirectLayers
open SignCube
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I]

def SignInput (P : I → X →L[ℝ] X) (C : ℝ) : Prop :=
  ∀ (m : ℕ) (T : Protocol X I m),T.Martingale → T.Nested →
    T.freshSum P ≤ C*(T.terminalEnergy+T.leakageSum P)

def PredictableInput (P : I → X →L[ℝ] X) (B : ℝ) : Prop :=
  ∀ (m : ℕ) (T : Protocol X I m),T.Martingale → T.Nested → T.Anchored → T.Supported P →
    ∀ C : ℝ,(∀ h,‖T.last h‖ ≤ C) → T.freshSum P ≤ B*C^2

def LeakageInput (P : I → X →L[ℝ] X) : Prop :=
  ∀ (m : ℕ) (T : Protocol X I m),T.Martingale → T.Nested → T.Anchored → T.CommonHeads →
    T.freshSum P ≤ 1024*(T.terminalEnergy+T.leakageSum P)
def GapInput (P : I → X →L[ℝ] X) : Prop :=
  ∀ (A B : I),A ≤ B → ∀ x y : X,P A x=x → P B y=y →
    ‖P B y-P A y‖^2 ≤ 400*((‖x+y‖^2+‖x-y‖^2)/2-‖x‖^2)

structure Regular (A : Midpoint.Heads I X) : Prop where
  nonempty : Nonempty I
  upper : ∀ H K : I,∃ J,H ≤ J ∧ K ≤ J
  nested_left : ∀ H K : I,H ≤ K → ∀ x : X,A.projection H (A.projection K x)=A.projection H x
  nested_right : ∀ H K : I,H ≤ K → ∀ x : X,A.projection K (A.projection H x)=A.projection H x
  contractive : ∀ H : I,∀ x : X,‖A.projection H x‖ ≤ ‖x‖
namespace Regular
variable {A : Midpoint.Heads I X} (hA : Regular A)
include hA
lemma finite_upper (S : Finset I) : ∃ B,∀ H ∈ S,H ≤ B := by
  classical
  induction S using Finset.induction_on with
  | empty => obtain ⟨B⟩ := hA.nonempty; exact ⟨B,by simp⟩
  | @insert H S hHS ih =>
    obtain ⟨K,hK⟩ := ih
    obtain ⟨B,hHB,hKB⟩ := hA.upper H K
    refine ⟨B,?_⟩
    intro J hJ
    rcases Finset.mem_insert.mp hJ with rfl|hJ
    · exact hHB
    · exact (hK J hJ).trans hKB
lemma tail_norm (H : I) (x : X) : ‖x-A.projection H x‖ ≤ 2*‖x‖ := by
  have hh := (norm_sub_le x (A.projection H x)).trans (add_le_add (le_refl _) (hA.contractive H x))
  linarith
/-- A single larger ancestral head captures any finite family. -/
lemma capture {κ : Type*} [Fintype κ] (H : I) (x : κ → X) {η : ℝ} (hη : 0 < η) :
    ∃ B : I,H ≤ B ∧ ∀ j,‖x j-A.projection B (x j)‖ < η := by
  classical
  choose K p hfix hclose using fun j => A.approximation (x j) (η/2) (half_pos hη)
  obtain ⟨B,hB⟩ := hA.finite_upper (insert H (Finset.univ.image K))
  refine ⟨B,hB H (Finset.mem_insert_self _ _),?_⟩
  intro j
  have hKB := hB (K j) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hBp : A.projection B (p j)=p j := by
    rw [← hfix j,hA.nested_right _ _ hKB]
  have he : x j-A.projection B (x j)=(x j-p j)-A.projection B (x j-p j) := by
    rw [map_sub,hBp]; abel
  rw [he]
  exact (hA.tail_norm B (x j-p j)).trans_lt (by linarith [hclose j])
lemma capture_one (H : I) (x : X) {η : ℝ} (hη : 0 < η) :
    ∃ B : I,H ≤ B ∧ ‖x-A.projection B x‖ < η := by
  obtain ⟨B,hHB,hB⟩ := hA.capture H (fun _ : Unit => x) hη
  exact ⟨B,hHB,hB ()⟩
lemma layer_parent (H B : I) (hHB : H ≤ B) (x : X) :
    ‖A.projection B x-A.projection H x‖ ≤ ‖x-A.projection H x‖ := by
  calc
    _ = ‖A.projection B (x-A.projection H x)‖ := by rw [map_sub,hA.nested_right H B hHB]
    _ ≤ _ := hA.contractive _ _
end Regular

lemma select_tail {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I] (A : Midpoint.Heads I X) (H : I) (z : ℕ → X) {R a r : ℝ}
    (hz : ∀ j,‖z j‖ ≤ R) (hs : ∀ i j,i ≠ j → a ≤ ‖z i-z j‖) (hr : r < a/2) :
    ∃ j,r < ‖z j-A.projection H (z j)‖ := by
  let := A.finite H
  by_contra! hn
  have hh := Midpoint.tail_packing (A.projection H) z hz hs hn
  linarith
end DirectLayers

namespace SignCube.Protocol
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
def initialEnergy : {n : ℕ} → Protocol X I n → ℝ
  | 0,.initial x _ => ‖x‖^2
  | _+1,.extend T _ _ _ => T.initialEnergy
lemma initialEnergy_nonneg {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} (T : Protocol X I n) : 0 ≤ T.initialEnergy := by
  induction T with | initial x H => exact sq_nonneg _ | extend T A B W ih => exact ih
variable [Preorder I]
lemma common_last {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I] {n : ℕ} (T : Protocol X I n) (h : T.CommonHeads) :
    ∃ H,∀ u,T.lastHead u=H := by
  cases T with
  | initial x H => exact ⟨H,fun _ => rfl⟩
  | extend T A B W => obtain ⟨H,hH⟩ := h.2; exact ⟨H,fun u => hH u.1⟩
lemma supported_last {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I] (P : I → X →L[ℝ] X) {n : ℕ} (T : Protocol X I n) (h : T.Supported P) :
    ∀ u,P (T.lastHead u) (T.last u)=T.last u := by
  cases T with
  | initial x H => exact fun _ => h
  | extend T A B W => exact fun u => h.2 u.1 u.2
end SignCube.Protocol

end DiamondDistortion

end

end OAI
