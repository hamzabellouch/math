import OAI.Analysis.AllenCahn.NormalizedJets

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff

lemma coordinateJet_mul_rest {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : List (Fin n)) (x : Space n) :
    coordinateJet (fun y => f y*g y) l x = f x*coordinateJet g l x+
      ((jetRestSplits l).map (fun p => coordinateJet f p.1 x*coordinateJet g p.2 x)).sum := by
  rw [coordinateJet_mul hf hg]
  have H := ((jetSplits_perm_rest l).map
    (fun p => coordinateJet f p.1 x*coordinateJet g p.2 x)).sum_eq
  simpa only [List.map_cons, List.sum_cons, coordinateJet] using H

lemma list_relative_sum_bound {α β X : Type*} (l : List α) (g : α → β → X → ℝ)
    (w : β → X → ℝ) (A : Set β)
    (hh : ∀ a ∈ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ A, ∀ x, |g a b x| ≤ C*w b x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ A, ∀ x, |(l.map (fun a => g a b x)).sum| ≤ C*w b x := by
  induction l with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons a l ih =>
    obtain ⟨M,hM,hMb⟩ := hh a (by simp)
    obtain ⟨N,hN,hNb⟩ := ih (fun c hc => hh c (by simp [hc]))
    refine ⟨M+N, add_nonneg hM hN, ?_⟩
    intro b hb x
    simp only [List.map_cons, List.sum_cons]
    calc |g a b x+(l.map (fun a => g a b x)).sum| ≤
        |g a b x|+|(l.map (fun a => g a b x)).sum| := abs_add_le _ _
      _ ≤ M*w b x+N*w b x := add_le_add (hMb b hb x) (hNb b hb x)
      _ = (M+N)*w b x := by ring

def JetControl {n : ℕ} {α : Type*} (S : Set α) (w f : α → Space n → ℝ) (k : ℕ) : Prop :=
  ∀ l : List (Fin n), l.length ≤ k → ∃ C : ℝ, 0 ≤ C ∧
    ∀ a ∈ S, ∀ x, |coordinateJet (f a) l x| ≤ C*w a x

lemma JetControl.mono_order {n : ℕ} {α : Type*} {S : Set α} {w f : α → Space n → ℝ}
    {k j : ℕ} (h : JetControl S w f k) (hj : j ≤ k) : JetControl S w f j :=
  fun l hl => h l (hl.trans hj)

lemma JetControl.mono_weight {n : ℕ} {α : Type*} {S : Set α} {w v f : α → Space n → ℝ}
    {k : ℕ} (h : JetControl S w f k) (hw : ∀ a ∈ S, ∀ x, w a x ≤ v a x) :
    JetControl S v f k := by
  intro l hl
  obtain ⟨C,hC,hb⟩ := h l hl
  exact ⟨C,hC,fun a ha x => (hb a ha x).trans (mul_le_mul_of_nonneg_left (hw a ha x) hC)⟩

lemma JetControl.const {n : ℕ} {α : Type*} (S : Set α) (c : ℝ) (k : ℕ) :
    JetControl S (fun _ _ => 1) (fun (_ : α) (_ : Space n) => c) k := by
  intro l hl
  refine ⟨|c|, abs_nonneg _, ?_⟩
  intro a ha x
  rw [coordinateJet_const]
  split_ifs <;> simp [abs_nonneg]

lemma JetControl.add {n : ℕ} {α : Type*} {S : Set α} {w f g : α → Space n → ℝ}
    {k : ℕ} (hf : ∀ a ∈ S, ContDiff ℝ ∞ (f a)) (hg : ∀ a ∈ S, ContDiff ℝ ∞ (g a))
    (h : JetControl S w f k) (h' : JetControl S w g k) :
    JetControl S w (fun a x => f a x+g a x) k := by
  intro l hl
  obtain ⟨C,hC,hb⟩ := h l hl
  obtain ⟨D,hD,hd⟩ := h' l hl
  refine ⟨C+D,add_nonneg hC hD, ?_⟩
  intro a ha x
  rw [coordinateJet_add (hf a ha) (hg a ha)]
  apply (abs_add_le _ _).trans
  simpa only [add_mul] using add_le_add (hb a ha x) (hd a ha x)

lemma JetControl.const_mul {n : ℕ} {α : Type*} {S : Set α} {w f : α → Space n → ℝ}
    {k : ℕ} (hf : ∀ a ∈ S, ContDiff ℝ ∞ (f a)) (h : JetControl S w f k) (c : ℝ) :
    JetControl S w (fun a x => c*f a x) k := by
  intro l hl
  obtain ⟨C,hC,hb⟩ := h l hl
  refine ⟨|c| * C,mul_nonneg (abs_nonneg _) hC, ?_⟩
  intro a ha x
  rw [coordinateJet_const_mul (hf a ha), abs_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb a ha x) (abs_nonneg c)

lemma JetControl.sub {n : ℕ} {α : Type*} {S : Set α} {w f g : α → Space n → ℝ}
    {k : ℕ} (hf : ∀ a ∈ S, ContDiff ℝ ∞ (f a)) (hg : ∀ a ∈ S, ContDiff ℝ ∞ (g a))
    (h : JetControl S w f k) (h' : JetControl S w g k) :
    JetControl S w (fun a x => f a x-g a x) k := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    h.add hf (fun a ha => contDiff_const.mul (hg a ha)) (h'.const_mul hg (-1))

lemma JetControl.mul {n : ℕ} {α : Type*} {S : Set α} {w v f g : α → Space n → ℝ}
    {k : ℕ} (hf : ∀ a ∈ S, ContDiff ℝ ∞ (f a)) (hg : ∀ a ∈ S, ContDiff ℝ ∞ (g a))
    (hw : ∀ a ∈ S, ∀ x, 0 ≤ w a x) (_hv : ∀ a ∈ S, ∀ x, 0 ≤ v a x)
    (h : JetControl S w f k) (h' : JetControl S v g k) :
    JetControl S (fun a x => w a x*v a x) (fun a x => f a x*g a x) k := by
  intro l hl
  obtain ⟨C,hC,hb⟩ := list_relative_sum_bound (jetSplits l)
    (fun p a x => coordinateJet (f a) p.1 x*coordinateJet (g a) p.2 x)
    (fun a x => w a x*v a x) S (by
      intro p hp
      obtain ⟨C,hC,hb⟩ := h p.1 ((jetSplits_length l p hp).1.trans hl)
      obtain ⟨D,hD,hd⟩ := h' p.2 ((jetSplits_length l p hp).2.trans hl)
      refine ⟨C*D,mul_nonneg hC hD, ?_⟩
      intro a ha x
      rw [abs_mul]
      have HH := mul_le_mul (hb a ha x) (hd a ha x) (abs_nonneg _) (mul_nonneg hC (hw a ha x))
      calc _ ≤ (C*w a x)*(D*v a x) := HH
        _ = (C*D)*(w a x*v a x) := by ring)
  refine ⟨C,hC, ?_⟩
  intro a ha x
  rw [coordinateJet_mul (hf a ha) (hg a ha)]
  exact hb a ha x

lemma JetControl.sum {n : ℕ} {α ι : Type*} {S : Set α} {w : α → Space n → ℝ}
    {f : ι → α → Space n → ℝ} {k : ℕ} (s : Finset ι)
    (hf : ∀ i ∈ s, ∀ a ∈ S, ContDiff ℝ ∞ (f i a))
    (hh : ∀ i ∈ s, JetControl S w (f i) k) :
    JetControl S w (fun a x => ∑ i ∈ s, f i a x) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro l hl
    refine ⟨0,le_rfl, ?_⟩
    intro a ha x
    simp only [Finset.sum_empty, coordinateJet_zero, abs_zero, zero_mul, le_refl]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hh i (by simp)).add (hf i (by simp))
      (fun a ha => ContDiff.sum (fun j hj => hf j (by simp [hj]) a ha))
      (ih (fun j hj => hf j (by simp [hj])) (fun j hj => hh j (by simp [hj])))

lemma JetControl.deriv {n : ℕ} {α : Type*} {S : Set α} {w f : α → Space n → ℝ}
    {k : ℕ} (hf : ∀ a ∈ S, ContDiff ℝ ∞ (f a)) (hh : JetControl S w f (k+1)) (i : Fin n) :
    JetControl S w (fun a => coordDeriv (f a) i) k := by
  intro l hl
  obtain ⟨C,hC,hb⟩ := hh (i::l) (by simp only [List.length_cons]; omega)
  refine ⟨C,hC, ?_⟩
  intro a ha x
  rw [coordinateJet_coordDeriv (hf a ha)]
  exact hb a ha x

lemma JetControl.of_zero {n : ℕ} {α : Type*} {S : Set α} {w f : α → Space n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hh : ∀ a ∈ S, ∀ x, |f a x| ≤ C*w a x) :
    JetControl S w f 0 := by
  intro l hl
  have he : l=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
  subst l
  exact ⟨C,hC,hh⟩

lemma finset_relative_sum_bound {α β X : Type*} (s : Finset α) (g : α → β → X → ℝ)
    (w : β → X → ℝ) (S : Set β)
    (hh : ∀ a ∈ s, ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ S, ∀ x, |g a b x| ≤ M*w b x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ S, ∀ x, |∑ a ∈ s, g a b x| ≤ M*w b x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨M,hM,hMb⟩ := hh a (by simp)
    obtain ⟨N,hN,hNb⟩ := ih (fun c hc => hh c (by simp [hc]))
    refine ⟨M+N,add_nonneg hM hN, ?_⟩
    intro b hb x
    rw [Finset.sum_insert ha]
    apply (abs_add_le _ _).trans
    simpa only [add_mul] using add_le_add (hMb b hb x) (hNb b hb x)

lemma coordinateJet_drift_system {n : ℕ} {f r : Space n → ℝ}
    {b : Space n → Space n} {bc : Fin n → Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hr : ContDiff ℝ ∞ r) (hc : ∀ i, ContDiff ℝ ∞ (bc i))
    (hb : ∀ (g : Space n → ℝ) x, fderiv ℝ g x (b x) = ∑ i, bc i x*coordDeriv g i x)
    (heq : ∀ x, Laplacian.laplacian f x-fderiv ℝ f x (b x) = r x)
    (l : List (Fin n)) (x : Space n) :
    Laplacian.laplacian (coordinateJet f l) x-fderiv ℝ (coordinateJet f l) x (b x) =
      coordinateJet r l x+∑ i : Fin n, ((jetRestSplits l).map (fun p =>
        coordinateJet (bc i) p.1 x*coordinateJet (coordDeriv f i) p.2 x)).sum := by
  have he : Laplacian.laplacian f = fun y => r y+∑ i, bc i y*coordDeriv f i y := by
    funext y
    rw [← hb f y]
    linarith [heq y]
  have ht (i : Fin n) := (hc i).mul (coordDeriv_smooth hf i)
  rw [coordinateJet_laplacian hf l, he,
    coordinateJet_add hr (ContDiff.sum (fun i _ => ht i)),
    coordinateJet_sum _ (fun i _ => ht i)]
  have hs : (∑ i : Fin n, coordinateJet (fun y => bc i y*coordDeriv f i y) l x) =
      ∑ i : Fin n, (bc i x*coordDeriv (coordinateJet f l) i x+
        ((jetRestSplits l).map (fun p => coordinateJet (bc i) p.1 x*
          coordinateJet (coordDeriv f i) p.2 x)).sum) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [coordinateJet_mul_rest (hc i) (coordDeriv_smooth hf i), coordinateJet_coordDeriv hf]
  dsimp only
  rw [hs, Finset.sum_add_distrib, hb]
  ring

lemma JetControl.bootstrap {n : ℕ} {α : Type*} {S : Set α}
    {w f r : α → Space n → ℝ} {b : α → Space n → Space n}
    {bc : Fin n → α → Space n → ℝ} {k : ℕ}
    (hf : ∀ a ∈ S, ContDiff ℝ ∞ (f a)) (hr : ∀ a ∈ S, ContDiff ℝ ∞ (r a))
    (hc : ∀ i a, a ∈ S → ContDiff ℝ ∞ (bc i a))
    (hw : ∀ a ∈ S, ContDiff ℝ 2 (w a)) (hp : ∀ a ∈ S, ∀ x, 0 < w a x)
    (hb : ∀ a ∈ S, ∀ (g : Space n → ℝ) x,
      fderiv ℝ g x (b a x) = ∑ i, bc i a x*coordDeriv g i x)
    (heq : ∀ a ∈ S, ∀ x, Laplacian.laplacian (f a) x-fderiv ℝ (f a) x (b a x) = r a x)
    {B G V : ℝ} (hB : 0 ≤ B) (hG : 0 ≤ G) (hV : 0 ≤ V)
    (hbb : ∀ a ∈ S, ∀ x, ‖b a x‖ ≤ B)
    (hwg : ∀ a ∈ S, ∀ x, ‖gradient (w a) x‖ ≤ G*w a x)
    (hwL : ∀ a ∈ S, ∀ x, |Laplacian.laplacian (w a) x-fderiv ℝ (w a) x (b a x)| ≤ V*w a x)
    (hJb : ∀ i, JetControl S (fun _ _ => 1) (bc i) k)
    (hJf : JetControl S w f k) (hJr : JetControl S w r k) :
    JetControl S w f (k+1) := by
  intro L hL
  cases L with
  | nil => exact hJf [] (by simp)
  | cons i l =>
    have hl : l.length ≤ k := by simp only [List.length_cons] at hL; omega
    obtain ⟨M,hM,hMb⟩ := hJf l hl
    obtain ⟨C,hC,hCb⟩ := hJr l hl
    obtain ⟨D,hD,hDb⟩ := finset_relative_sum_bound (Finset.univ : Finset (Fin n))
      (fun j a x => ((jetRestSplits l).map (fun p => coordinateJet (bc j a) p.1 x*
        coordinateJet (coordDeriv (f a) j) p.2 x)).sum) w S (by
        intro j hj
        apply list_relative_sum_bound
        intro p hp'
        obtain ⟨h1,h2⟩ := jetRestSplits_length l p hp'
        obtain ⟨A,hA,hAb⟩ := hJb j p.1 (h1.trans hl)
        obtain ⟨N,hN,hNb⟩ := hJf (j::p.2) (by simp only [List.length_cons]; omega)
        refine ⟨A*N,mul_nonneg hA hN, ?_⟩
        intro a ha x
        rw [abs_mul, coordinateJet_coordDeriv (hf a ha)]
        have ha' : |coordinateJet (bc j a) p.1 x| ≤ A := by simpa using hAb a ha x
        have hh := mul_le_mul ha' (hNb a ha x) (abs_nonneg _) hA
        simpa only [coordinateJet, mul_assoc] using hh)
    let C' := C+D
    have hC' : 0 ≤ C' := add_nonneg hC hD
    refine ⟨2*(2*M+(C'+M*V)+3)*(B+2*G+1)+M*G, by positivity, ?_⟩
    intro a ha x
    have hx (y) : |Laplacian.laplacian (coordinateJet (f a) l) y-
        fderiv ℝ (coordinateJet (f a) l) y (b a y)| ≤ C'*w a y := by
      rw [coordinateJet_drift_system (hf a ha) (hr a ha) (fun j => hc j a ha) (hb a ha) (heq a ha)]
      apply (abs_add_le _ _).trans
      simpa only [C', add_mul] using add_le_add (hCb a ha y) (hDb a ha y)
    apply (coordDeriv_abs_le_gradient _ _ _).trans
    exact carrier_gradient_estimate (smooth_C2 (coordinateJet_smooth (hf a ha) l))
      (hw a ha) (hp a ha) (b a) hM hC' hB hG hV (hMb a ha) (hbb a ha) (hwg a ha)
      hx (hwL a ha) x

lemma JetControl.congr {n : ℕ} {α : Type*} {S : Set α} {w f g : α → Space n → ℝ}
    {k : ℕ} (h : JetControl S w f k) (he : ∀ a ∈ S, f a = g a) : JetControl S w g k := by
  intro l hl
  obtain ⟨C,hC,hb⟩ := h l hl
  exact ⟨C,hC,fun a ha x => by rw [← he a ha]; exact hb a ha x⟩

lemma JetControl.of_derivs {n : ℕ} {α : Type*} {S : Set α} {w f : α → Space n → ℝ}
    {k : ℕ} (hf : ∀ a ∈ S, ContDiff ℝ ∞ (f a)) (h0 : JetControl S w f 0)
    (hh : ∀ i, JetControl S w (fun a => coordDeriv (f a) i) k) : JetControl S w f (k+1) := by
  intro l hl
  cases l with
  | nil => exact h0 [] (by simp)
  | cons i l =>
    obtain ⟨C,hC,hb⟩ := hh i l (by simp only [List.length_cons] at hl; omega)
    refine ⟨C,hC,fun a ha x => ?_⟩
    have H := hb a ha x
    rw [coordinateJet_coordDeriv (hf a ha)] at H
    exact H

lemma JetControl.mul_bounded {n : ℕ} {α : Type*} {S : Set α} {w f g : α → Space n → ℝ}
    {k : ℕ} (hf : ∀ a ∈ S, ContDiff ℝ ∞ (f a)) (hg : ∀ a ∈ S, ContDiff ℝ ∞ (g a))
    (hw : ∀ a ∈ S, ∀ x, 0 ≤ w a x) (h : JetControl S (fun _ _ => 1) f k)
    (h' : JetControl S w g k) : JetControl S w (fun a x => f a x*g a x) k := by
  simpa only [one_mul] using h.mul hf hg (fun _ _ _ => zero_le_one) hw h'

def positiveDefectClass (n : ℕ) : Set (Space n → ℝ) :=
  {v | ContDiff ℝ ∞ v ∧ (∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1) ∧ AllenCahn v ∧
    ∀ x, 0 < diffuseDefect v x}

lemma positiveDefectClass_smooth {n : ℕ} {v : Space n → ℝ} (hv : v ∈ positiveDefectClass n) :
    ContDiff ℝ ∞ v := hv.1

lemma positiveDefectClass_interior {n : ℕ} {v : Space n → ℝ} (hv : v ∈ positiveDefectClass n) :
    ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1 := hv.2.1

lemma positiveDefectClass_pde {n : ℕ} {v : Space n → ℝ} (hv : v ∈ positiveDefectClass n) :
    AllenCahn v := hv.2.2.1

lemma positiveDefectClass_positive {n : ℕ} {v : Space n → ℝ} (hv : v ∈ positiveDefectClass n) :
    ∀ x, 0 < diffuseDefect v x := hv.2.2.2

lemma defect_le_root {n : ℕ} {v : Space n → ℝ} (hv : v ∈ positiveDefectClass n) (x : Space n) :
    diffuseDefect v x ≤ defectRoot v x := by
  nlinarith [defectRoot_sq (hv.2.2.2 x), defectRoot_pos v x, defectRoot_le_one hv.2.2.2 x]

lemma positiveAC_jet_base (n : ℕ) :
    JetControl (positiveDefectClass n) (fun _ _ => 1) (fun v => v) 0 ∧
    (∀ i, JetControl (positiveDefectClass n) (fun _ _ => 1)
      (fun v => coordDeriv (inverseProfile v) i) 0) ∧
    JetControl (positiveDefectClass n) diffuseDefect diffuseDefect 0 ∧
    ∀ i j, JetControl (positiveDefectClass n) defectRoot (fun v => inverseHessian v i j) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply JetControl.of_zero (C := 1) zero_le_one
    intro v hv x
    simpa using (abs_le.mpr ⟨(hv.2.1 x).1.le,(hv.2.1 x).2.le⟩)
  · intro i
    apply JetControl.of_zero (C := 1) zero_le_one
    intro v hv x
    simpa using (coordDeriv_abs_le_gradient (inverseProfile v) i x).trans
      (inverseProfile_gradient_bound (smooth_C2 hv.1) hv.2.1 hv.2.2.1 x)
  · apply JetControl.of_zero (C := 1) zero_le_one
    intro v hv x
    simp only [one_mul, abs_of_pos (hv.2.2.2 x), le_refl]
  · intro i j
    apply JetControl.of_zero (C := Real.sqrt (tensorBernsteinConstant n+3)) (Real.sqrt_nonneg _)
    intro v hv x
    exact (inverseHessian_abs_le_sqrt v i j x).trans
      (normalized_tensor_square_bounds hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 x).1

lemma positiveAC_root_product {n : ℕ} {f g : (Space n → ℝ) → Space n → ℝ} {k : ℕ}
    (hf : ∀ v ∈ positiveDefectClass n, ContDiff ℝ ∞ (f v))
    (hg : ∀ v ∈ positiveDefectClass n, ContDiff ℝ ∞ (g v))
    (h : JetControl (positiveDefectClass n) defectRoot f k)
    (h' : JetControl (positiveDefectClass n) defectRoot g k) :
    JetControl (positiveDefectClass n) diffuseDefect (fun v x => f v x*g v x) k := by
  have H := h.mul hf hg (fun v _ x => (defectRoot_pos v x).le)
    (fun v _ x => (defectRoot_pos v x).le) h'
  intro l hl
  obtain ⟨C,hC,hb⟩ := H l hl
  refine ⟨C,hC,fun v hv x => ?_⟩
  simpa only [← pow_two, defectRoot_sq (hv.2.2.2 x)] using hb v hv x

end DeGiorgi
end

end OAI
