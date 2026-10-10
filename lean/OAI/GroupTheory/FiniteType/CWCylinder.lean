import Mathlib

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
namespace CWCylinder
universe u
variable {Y : Type u} [TopologicalSpace Y]
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Boundary (n : ℕ) := sphere (0 : Fin n → ℝ) 1

theorem norm_cons {n : ℕ} (a : ℝ) (v : Fin n → ℝ) :
    ‖(Fin.cons a v : Fin (n+1) → ℝ)‖ = max ‖a‖ ‖v‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg a) (le_max_left _ _))]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact (by simpa using norm_le_pi_norm v j : ‖(Fin.cons a v : Fin (n+1) → ℝ) j.succ‖ ≤ ‖v‖).trans (le_max_right _ _)
  · apply max_le
    · simpa using norm_le_pi_norm (Fin.cons a v : Fin (n+1) → ℝ) 0
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      simpa using norm_le_pi_norm (Fin.cons a v : Fin (n+1) → ℝ) j.succ

theorem norm_tail_le {n : ℕ} (v : Fin (n+1) → ℝ) : ‖Fin.tail v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j
  exact norm_le_pi_norm v j.succ

theorem norm_eq_max {n : ℕ} (v : Fin (n+1) → ℝ) :
    ‖v‖ = max ‖v 0‖ ‖Fin.tail v‖ := by
  have he : Fin.cons (v 0) (Fin.tail v) = v := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  simpa only [he] using norm_cons (v 0) (Fin.tail v)

theorem time_bound (t : I) : ‖2*(t:ℝ)-1‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> linarith [t.2.1,t.2.2]

def encode (n : ℕ) : C(I × Disk n,Disk (n+1)) :=
  ⟨fun z => ⟨Fin.cons (2*(z.1:ℝ)-1) z.2,by
      rw [mem_closedBall,dist_zero_right,norm_cons]
      exact max_le (time_bound z.1) (by simpa only [mem_closedBall,dist_zero_right] using z.2.2)⟩,
    (continuous_pi (fun i => Fin.cases (by fun_prop) (fun j => by fun_prop) i)).subtype_mk _⟩

def diskTail (n : ℕ) : C(Disk (n+1),Disk n) :=
  ⟨fun v => ⟨Fin.tail v.1,by
      rw [mem_closedBall,dist_zero_right]
      exact (norm_tail_le v.1).trans (by simpa only [mem_closedBall,dist_zero_right] using v.2)⟩,
    (by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro j
      exact (continuous_apply j.succ).comp continuous_subtype_val)⟩

def diskTime (n : ℕ) : C(Disk (n+1),I) :=
  ⟨fun v => ⟨(v.1 0 + 1)/2,by
      have hv : ‖v.1 0‖ ≤ 1 := (norm_le_pi_norm v.1 0).trans
        (by simpa only [mem_closedBall,dist_zero_right] using v.2)
      rw [Real.norm_eq_abs,abs_le] at hv
      constructor <;> linarith [hv.1,hv.2]⟩,
    (by
      apply Continuous.subtype_mk
      exact (((continuous_apply (0 : Fin (n+1))).comp continuous_subtype_val).add continuous_const).div_const 2)⟩

@[simp] theorem encode_tail (n : ℕ) (z : I × Disk n) : diskTail n (encode n z) = z.2 := by
  apply Subtype.ext
  funext i
  rfl

@[simp] theorem encode_time (n : ℕ) (z : I × Disk n) : diskTime n (encode n z) = z.1 := by
  apply Subtype.ext
  change ((2*(z.1:ℝ)-1)+1)/2 = (z.1:ℝ)
  ring

theorem encode_decode (n : ℕ) (v : Disk (n+1)) : encode n (diskTime n v,diskTail n v) = v := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  change 2*((v.1 0 + 1)/2)-1 = v.1 0
  ring

theorem encode_injective (n : ℕ) : Function.Injective (encode n) := by
  intro a b h
  exact Prod.ext (by simpa using congrArg (diskTime n) h) (by simpa using congrArg (diskTail n) h)

def bottom (n : ℕ) : C(Disk n,Boundary (n+1)) :=
  ⟨fun v => ⟨Fin.cons (-1) v,by
      rw [mem_sphere,dist_zero_right,norm_cons]
      have hv : ‖(v : Fin n → ℝ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
      simp only [norm_neg,norm_one,max_eq_left hv]⟩,
    (continuous_pi (fun i => Fin.cases continuous_const (fun j => by fun_prop) i)).subtype_mk _⟩

def top (n : ℕ) : C(Disk n,Boundary (n+1)) :=
  ⟨fun v => ⟨Fin.cons 1 v,by
      rw [mem_sphere,dist_zero_right,norm_cons]
      have hv : ‖(v : Fin n → ℝ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
      simp only [norm_one,max_eq_left hv]⟩,
    (continuous_pi (fun i => Fin.cases continuous_const (fun j => by fun_prop) i)).subtype_mk _⟩

def side (n : ℕ) : C(I × Boundary n,Boundary (n+1)) :=
  ⟨fun z => ⟨Fin.cons (2*(z.1:ℝ)-1) z.2,by
      rw [mem_sphere,dist_zero_right,norm_cons]
      have hv : ‖(z.2 : Fin n → ℝ)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using z.2.2
      rw [hv,max_eq_right (time_bound z.1)]⟩,
    (continuous_pi (fun i => Fin.cases (by fun_prop) (fun j => by fun_prop) i)).subtype_mk _⟩

abbrev Faces (n : ℕ) := Disk n ⊕ (Disk n ⊕ (I × Boundary n))

def faceQuot (n : ℕ) : C(Faces n, Boundary (n+1)) :=
  ⟨Sum.elim (bottom n) (Sum.elim (top n) (side n)),
    continuous_sum_dom.mpr ⟨(bottom n).continuous,
      continuous_sum_dom.mpr ⟨(top n).continuous,(side n).continuous⟩⟩⟩

theorem faceQuot_surjective (n : ℕ) : Function.Surjective (faceQuot n) := by
  intro v
  let d : Disk (n+1) := ⟨v,sphere_subset_closedBall v.2⟩
  by_cases h0 : v.1 0 = -1
  · refine ⟨Sum.inl (diskTail n d),?_⟩
    apply Subtype.ext
    funext i
    exact Fin.cases h0.symm (fun _ => rfl) i
  by_cases h1 : v.1 0 = 1
  · refine ⟨Sum.inr (Sum.inl (diskTail n d)),?_⟩
    apply Subtype.ext
    funext i
    exact Fin.cases h1.symm (fun _ => rfl) i
  have ht : ‖Fin.tail v.1‖ = 1 := by
    have hv : max ‖v.1 0‖ ‖Fin.tail v.1‖ = 1 := by
      rw [← norm_eq_max]
      simpa only [mem_sphere,dist_zero_right] using v.2
    have hh : ‖v.1 0‖ ≠ 1 := by
      intro hh
      rw [Real.norm_eq_abs] at hh
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hh with hh | hh
      · exact h1 hh
      · exact h0 hh
    exact (max_eq_iff.mp hv).resolve_left (fun h => hh h.1) |>.1
  refine ⟨Sum.inr (Sum.inr (diskTime n d,⟨Fin.tail v.1,by simpa only [mem_sphere,dist_zero_right] using ht⟩)),?_⟩
  apply Subtype.ext
  have he := congrArg Subtype.val (encode_decode n d)
  exact he

theorem faceQuot_isQuotientMap (n : ℕ) : IsQuotientMap (faceQuot n) :=
  IsQuotientMap.of_surjective_continuous (faceQuot_surjective n) (faceQuot n).continuous

def boundaryDisk (n : ℕ) : C(Boundary n,Disk n) :=
  ⟨fun v => ⟨v,sphere_subset_closedBall v.2⟩,continuous_subtype_val.subtype_mk _⟩

def faceCylinder (n : ℕ) : Faces n → I × Disk n :=
  Sum.elim (fun v => (0,v)) (Sum.elim (fun v => (1,v)) (fun z => (z.1,boundaryDisk n z.2)))

theorem face_encode (n : ℕ) (v : Faces n) :
    encode n (faceCylinder n v) = boundaryDisk (n+1) (faceQuot n v) := by
  rcases v with v | v | v
  · apply Subtype.ext
    change (Fin.cons ((2:ℝ)*0-1) v : Fin (n+1) → ℝ) = Fin.cons (-1) v
    norm_num
  · apply Subtype.ext
    change (Fin.cons ((2:ℝ)*1-1) v : Fin (n+1) → ℝ) = Fin.cons 1 v
    norm_num
  · rfl

theorem faceCylinder_eq_of_faceQuot_eq (n : ℕ) {a b : Faces n}
    (h : faceQuot n a = faceQuot n b) : faceCylinder n a = faceCylinder n b := by
  apply encode_injective n
  rw [face_encode,face_encode,h]

def faceData {n : ℕ} (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y)) : C(Faces n,Y) :=
  ⟨Sum.elim f₀ (Sum.elim f₁ h),continuous_sum_dom.mpr
    ⟨f₀.continuous,continuous_sum_dom.mpr ⟨f₁.continuous,h.continuous⟩⟩⟩

theorem faceData_factors {n : ℕ} (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (boundaryDisk n v)) :
    Function.FactorsThrough (faceData f₀ f₁ h) (faceQuot n) := by
  intro a b he
  have hc := faceCylinder_eq_of_faceQuot_eq n he
  rcases a with a | a | a <;> rcases b with b | b | b
  · exact congrArg f₀ (congrArg Prod.snd hc)
  · have he : (0 : I) = 1 := congrArg Prod.fst hc
    exact (zero_ne_one he).elim
  · have ht : b.1 = 0 := (congrArg Prod.fst hc).symm
    have hv : a = boundaryDisk n b.2 := congrArg Prod.snd hc
    change f₀ a = h b
    rw [hv,← h₀]
    exact congrArg h (Prod.ext ht.symm rfl)
  · have he : (1 : I) = 0 := congrArg Prod.fst hc
    exact (one_ne_zero he).elim
  · exact congrArg f₁ (congrArg Prod.snd hc)
  · have ht : b.1 = 1 := (congrArg Prod.fst hc).symm
    have hv : a = boundaryDisk n b.2 := congrArg Prod.snd hc
    change f₁ a = h b
    rw [hv,← h₁]
    exact congrArg h (Prod.ext ht.symm rfl)
  · have ht : a.1 = 0 := congrArg Prod.fst hc
    have hv : boundaryDisk n a.2 = b := congrArg Prod.snd hc
    change h a = f₀ b
    rw [← hv,← h₀]
    exact congrArg h (Prod.ext ht rfl)
  · have ht : a.1 = 1 := congrArg Prod.fst hc
    have hv : boundaryDisk n a.2 = b := congrArg Prod.snd hc
    change h a = f₁ b
    rw [← hv,← h₁]
    exact congrArg h (Prod.ext ht rfl)
  · apply congrArg h
    apply Prod.ext
    · exact congrArg (fun z : I × Disk n => z.1) hc
    · exact Subtype.ext (congrArg (fun z : I × Disk n => (z.2 : Fin n → ℝ)) hc)

def boundaryMap {n : ℕ} (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (boundaryDisk n v)) : C(Boundary (n+1),Y) :=
  (faceQuot_isQuotientMap n).lift (faceData f₀ f₁ h) (faceData_factors f₀ f₁ h h₀ h₁)

theorem boundaryMap_face {n : ℕ} (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (boundaryDisk n v)) (v : Faces n) :
    boundaryMap f₀ f₁ h h₀ h₁ (faceQuot n v) = faceData f₀ f₁ h v :=
  DFunLike.congr_fun ((faceQuot_isQuotientMap n).lift_comp (faceData f₀ f₁ h) (faceData_factors f₀ f₁ h h₀ h₁)) v

def SphereFill (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ n (f : C(Boundary n,Y)), ∃ g : C(Disk n,Y), ∀ v, g (boundaryDisk n v) = f v

theorem exists_cylinder (hfill : SphereFill Y) {n : ℕ}
    (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (boundaryDisk n v)) :
    ∃ F : C(I × Disk n,Y),
      (∀ v, F (0,v) = f₀ v) ∧ (∀ v, F (1,v) = f₁ v) ∧
      ∀ t v, F (t,boundaryDisk n v) = h (t,v) := by
  obtain ⟨g,hg⟩ := hfill (n+1) (boundaryMap f₀ f₁ h h₀ h₁)
  refine ⟨g.comp (encode n),?_,?_,?_⟩
  · intro v
    change g (encode n (0,v)) = _
    rw [show (0,v) = faceCylinder n (Sum.inl v) from rfl,face_encode,hg]
    exact boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inl v)
  · intro v
    change g (encode n (1,v)) = _
    rw [show (1,v) = faceCylinder n (Sum.inr (Sum.inl v)) from rfl,face_encode,hg]
    exact boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inr (Sum.inl v))
  · intro t v
    change g (encode n (t,boundaryDisk n v)) = _
    rw [show (t,boundaryDisk n v) = faceCylinder n (Sum.inr (Sum.inr (t,v))) from rfl,face_encode,hg]
    exact boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inr (Sum.inr (t,v)))

end CWCylinder

end

end OAI
