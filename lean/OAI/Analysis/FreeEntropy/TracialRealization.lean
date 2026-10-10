import OAI.Analysis.FreeEntropy.MatrixScoreWords

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
theorem commute_add_star_of_boundary {A : Type u1} [Ring A] [StarRing A]
    (l r q : A) (hlr : Commute l r)
    (hrl : star r * l = l * star r + q) (hq : star q = q) :
    Commute (l + star l) (r + star r) := by
  have hls : star l * r = r * star l + q := by
    simpa only [star_mul, star_add, star_star, hq] using congrArg star hrl
  have hss : star l * star r = star r * star l := hlr.star_star.eq
  show _ * _ = _ * _
  simp only [add_mul, mul_add]
  rw [hlr.eq, hls, hss, hrl]
  abel

namespace LabelHilbert
variable {α : Type} [DecidableEq α]

theorem lift_id : lift (id : α → α) Function.injective_id = 1 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro a
  apply ContinuousLinearMap.ext
  intro z
  simp

theorem lift_inverse (f g : α → α) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : Function.LeftInverse g f) (hgf : Function.RightInverse g f) :
    star (lift f hf) = lift g hg := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro a
  apply ContinuousLinearMap.ext
  intro z
  change star (lift f hf) (lp.single 2 a z) = lift g hg (lp.single 2 a z)
  rw [adjoint_single_of_inverse f hf (fun b => some (g b)), lift_single]
  · rfl
  · intro a b
    simp only [Option.some.injEq]
    constructor
    · intro h
      rw [← h, hgf b]
    · intro h
      rw [← h, hfg a]

def keepLinear (P : α → Prop) [DecidablePred P] : Space α →ₗ[ℂ] Space α where
  toFun x := ⟨fun a => if P a then x a else 0, (lp.memℓp x).mono' (by
    intro a
    split_ifs <;> simp)⟩
  map_add' x y := by
    apply lp.ext
    funext a
    change (if P a then x a + y a else 0) =
      (if P a then x a else 0) + (if P a then y a else 0)
    by_cases h : P a <;> simp [h]
  map_smul' c x := by
    apply lp.ext
    funext a
    by_cases h : P a <;> simp [h]

def keep (P : α → Prop) [DecidablePred P] : Space α →L[ℂ] Space α :=
  (keepLinear P).mkContinuous 1 (by
    intro x
    simp only [one_mul]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro a
    change ‖if P a then x a else 0‖ ≤ ‖x a‖
    split_ifs <;> simp)

omit [DecidableEq α] in
@[simp] theorem keep_apply (P : α → Prop) [DecidablePred P] (x : Space α) (a : α) :
    keep P x a = if P a then x a else 0 := rfl

 theorem keep_single (P : α → Prop) [DecidablePred P] (a : α) (z : ℂ) :
    keep P (lp.single 2 a z) = if P a then lp.single 2 a z else 0 := by
  apply lp.ext
  funext b
  by_cases h : b = a
  · subst b; split_ifs <;> simp_all
  · by_cases ha : P a <;> by_cases hb : P b <;>
      simp [ha, hb, lp.single_apply, h]

@[simp] theorem star_keep (P : α → Prop) [DecidablePred P] : star (keep P) = keep P := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext a
  have h := ContinuousLinearMap.adjoint_inner_right (keep P) (basis a) x
  change inner ℂ (basis a) (star (keep P) x) = inner ℂ (keep P (basis a)) x at h
  rw [basis, keep_single] at h
  by_cases ha : P a <;> simpa [ha, lp.inner_single_left] using h

end LabelHilbert
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
@[simp] theorem leftG_one (w : Word B N G) : leftG 1 w = w := by
  rcases w with ⟨⟨v,g⟩,t⟩
  simp [leftG]

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
@[simp] theorem leftG_mul (g h : G) (w : Word B N G) :
    leftG (g*h) w = leftG g (leftG h w) := by
  simp [leftG, mul_assoc]

@[simp] theorem unitaryG_one : unitaryG (B := B) (N := N) (1 : G) = 1 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro a
  apply ContinuousLinearMap.ext
  intro z
  change unitaryG 1 (lp.single 2 a z) = lp.single 2 a z
  rw [unitaryG_single, leftG_one]

@[simp] theorem unitaryG_mul (g h : G) :
    unitaryG (B := B) (N := N) (g*h) = unitaryG g * unitaryG h := by
  unfold unitaryG
  rw [LabelHilbert.lift_mul]
  congr 1
  exact funext (leftG_mul g h)

@[simp] theorem star_unitaryG (g : G) :
    star (unitaryG (B := B) (N := N) g) = unitaryG g⁻¹ := by
  apply LabelHilbert.lift_inverse
  · intro w; rw [← leftG_mul]; simp
  · intro w; rw [← leftG_mul]; simp

@[simp] theorem star_rightUnitaryG (g : G) :
    star (rightUnitaryG (B := B) (N := N) g) = rightUnitaryG g⁻¹ := by
  apply LabelHilbert.lift_inverse
  · intro w; simp [rightG, ← leftG_mul]
  · intro w; simp [rightG, ← leftG_mul]

 theorem unitaryG_commutes_rightCreationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (rightCreationB b) :=
  LabelHilbert.lift_commute _ _ _ _ (leftG_rightB g b)

 theorem unitaryG_commutes_rightCreationN (g : G) (i : N) :
    Commute (unitaryG (B := B) g) (rightCreationN i) :=
  LabelHilbert.lift_commute _ _ _ _ (leftG_rightN g i)

 theorem creationB_commutes_rightUnitaryG (b : B) (g : G) :
    Commute (creationB (N := N) b) (rightUnitaryG g) :=
  LabelHilbert.lift_commute _ _ _ _ (leftB_rightG b g)

 theorem creationN_commutes_rightUnitaryG (i : N) (g : G) :
    Commute (creationN (B := B) i) (rightUnitaryG g) :=
  LabelHilbert.lift_commute _ _ _ _ (leftN_rightG i g)

 theorem unitaryG_commutes_rightUnitaryG (g h : G) :
    Commute (unitaryG (B := B) (N := N) g) (rightUnitaryG h) :=
  LabelHilbert.lift_commute _ _ _ _ (leftG_rightG g h)

 theorem unitaryG_commutes_rightAnnihilationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (star (rightCreationB b)) := by
  have h := (unitaryG_commutes_rightCreationB (N := N) g⁻¹ b).star_star
  simpa using h

 theorem unitaryG_commutes_rightAnnihilationN (g : G) (i : N) :
    Commute (unitaryG (B := B) g) (star (rightCreationN i)) := by
  have h := (unitaryG_commutes_rightCreationN (B := B) g⁻¹ i).star_star
  simpa using h

 theorem annihilationB_commutes_rightUnitaryG (b : B) (g : G) :
    Commute (star (creationB (N := N) b)) (rightUnitaryG g) := by
  have h := (creationB_commutes_rightUnitaryG (N := N) b g⁻¹).star_star
  simpa using h

 theorem annihilationN_commutes_rightUnitaryG (i : N) (g : G) :
    Commute (star (creationN (B := B) i)) (rightUnitaryG g) := by
  have h := (creationN_commutes_rightUnitaryG (B := B) i g⁻¹).star_star
  simpa using h

def signalBoundary : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.keep (fun w : Word B N G => w.1.1 = [] ∧ w.2 = [])

def vacuumBoundary : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.keep (fun w : Word B N G => w = empty)

omit [Group G] in
@[simp] theorem signalBoundary_single (w : Word B N G) (z : ℂ) :
    signalBoundary (lp.single 2 w z) =
      if w.1.1 = [] ∧ w.2 = [] then lp.single 2 w z else 0 :=
  LabelHilbert.keep_single _ _ _

@[simp] theorem vacuumBoundary_single (w : Word B N G) (z : ℂ) :
    vacuumBoundary (lp.single 2 w z) = if w = empty then lp.single 2 w z else 0 :=
  LabelHilbert.keep_single _ _ _

 theorem rightAnnihilationN_creationN (i j : N) :
    star (rightCreationN (B := B) (G := G) i) * creationN j =
      creationN j * star (rightCreationN i) + if i = j then vacuumBoundary else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreationN i) (creationN j (lp.single 2 w z)) =
    creationN j (star (rightCreationN i) (lp.single 2 w z)) +
      (if i = j then vacuumBoundary else 0) (lp.single 2 w z)
  rcases w with ⟨a,t⟩
  induction t using List.reverseRecOn with
  | nil =>
    rw [rightAnnihilationN_atom, map_zero, zero_add, creationN_single]
    change star (rightCreationN i) (lp.single 2 (append empty j a) z) = _
    rw [rightAnnihilationN_append]
    by_cases ha : a = ([],1) <;> by_cases hij : i = j <;>
      simp [ha, hij, empty]
  | append_singleton t c _ =>
    rcases c with ⟨k,c⟩
    rw [creationN_single]
    change star (rightCreationN i) (lp.single 2 (append (leftN j (a,t)) k c) z) =
      creationN j (star (rightCreationN i) (lp.single 2 (append (a,t) k c) z)) + _
    rw [rightAnnihilationN_append, rightAnnihilationN_append]
    by_cases hij : i = j <;> simp only [hij, ↓reduceIte, zero_apply]
    all_goals simp only [vacuumBoundary_single, empty, Prod.mk.injEq,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceIte, add_zero]
    all_goals split_ifs <;> simp

 theorem rightAnnihilationB_creationB_atom (b c : B) (v : List B) (g : G) (z : ℂ) :
    star (rightCreationB (N := N) b) (creationB c (lp.single 2 ((v,g),[]) z)) =
      creationB c (star (rightCreationB b) (lp.single 2 ((v,g),[]) z)) +
        (if b = c then signalBoundary else 0) (lp.single 2 ((v,g),[]) z) := by
  induction v using List.reverseRecOn with
  | nil =>
    rw [rightAnnihilationB_atom_nil, map_zero, zero_add, creationB_single]
    simp only [leftB]
    rw [show [c] = [] ++ [c] from rfl, rightAnnihilationB_atom_append]
    by_cases h : b = c <;> simp only [h, ↓reduceIte, signalBoundary_single,
      and_self, zero_apply]
  | append_singleton v a _ =>
    rw [rightAnnihilationB_atom_append, creationB_single]
    simp only [leftB] at *
    rw [show c :: (v ++ [a]) = (c :: v) ++ [a] from rfl, rightAnnihilationB_atom_append]
    by_cases hc : b = c <;> simp only [hc, ↓reduceIte, signalBoundary_single,
      List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_and,
      zero_apply, add_zero]
    all_goals split_ifs <;> simp [leftB]

 theorem rightAnnihilationB_creationB_append (b c : B) (w : Word B N G) (i : N)
    (a : Atom B G) (z : ℂ) :
    star (rightCreationB b) (creationB c (lp.single 2 (append w i a) z)) =
      creationB c (star (rightCreationB b) (lp.single 2 (append w i a) z)) := by
  rcases a with ⟨v,g⟩
  rw [creationB_single]
  change star (rightCreationB b) (lp.single 2 (append (leftB c w) i (v,g)) z) = _
  induction v using List.reverseRecOn with
  | nil => rw [rightAnnihilationB_append_nil, rightAnnihilationB_append_nil, map_zero]
  | append_singleton v a _ =>
    rw [rightAnnihilationB_append_append, rightAnnihilationB_append_append]
    by_cases h : b = a <;> simp only [h, ↓reduceIte, map_zero, creationB_single]
    rfl

 theorem rightAnnihilationB_creationB (b c : B) :
    star (rightCreationB (N := N) (G := G) b) * creationB c =
      creationB c * star (rightCreationB b) + if b = c then signalBoundary else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreationB b) (creationB c (lp.single 2 w z)) =
    creationB c (star (rightCreationB b) (lp.single 2 w z)) +
      (if b = c then signalBoundary else 0) (lp.single 2 w z)
  rcases w with ⟨⟨v,g⟩,t⟩
  induction t using List.reverseRecOn with
  | nil => exact rightAnnihilationB_creationB_atom b c v g z
  | append_singleton t d _ =>
    rcases d with ⟨k,a⟩
    change star (rightCreationB b) (creationB c (lp.single 2 (append ((v,g),t) k a) z)) = _
    rw [rightAnnihilationB_creationB_append]
    by_cases h : b = c <;> simp [h, append]

def semicircularB (b : B) : Space B N G →L[ℂ] Space B N G := creationB b + star (creationB b)
def semicircularN (i : N) : Space B N G →L[ℂ] Space B N G := creationN i + star (creationN i)
def rightSemicircularB (b : B) : Space B N G →L[ℂ] Space B N G :=
  rightCreationB b + star (rightCreationB b)
def rightSemicircularN (i : N) : Space B N G →L[ℂ] Space B N G :=
  rightCreationN i + star (rightCreationN i)

omit [Group G] in
@[simp] theorem star_semicircularB (b : B) :
    star (semicircularB (N := N) (G := G) b) = semicircularB b := by
  exact IsSelfAdjoint.add_star_self (creationB b)
@[simp] theorem star_semicircularN (i : N) :
    star (semicircularN (B := B) (G := G) i) = semicircularN i := by
  exact IsSelfAdjoint.add_star_self (creationN i)
@[simp] theorem star_rightSemicircularB (b : B) :
    star (rightSemicircularB (N := N) (G := G) b) = rightSemicircularB b := by
  exact IsSelfAdjoint.add_star_self (rightCreationB b)
@[simp] theorem star_rightSemicircularN (i : N) :
    star (rightSemicircularN (B := B) (G := G) i) = rightSemicircularN i := by
  exact IsSelfAdjoint.add_star_self (rightCreationN i)

 theorem semicircularB_commutes_rightB (b c : B) :
    Commute (semicircularB (N := N) (G := G) b) (rightSemicircularB c) := by
  apply commute_add_star_of_boundary _ _ _
    (LabelHilbert.lift_commute _ _ _ _ (leftB_rightB b c))
    (rightAnnihilationB_creationB c b)
  split_ifs <;> simp [signalBoundary]

 theorem semicircularN_commutes_rightN (i j : N) :
    Commute (semicircularN (B := B) (G := G) i) (rightSemicircularN j) := by
  apply commute_add_star_of_boundary _ _ _
    (LabelHilbert.lift_commute _ _ _ _ (leftN_rightN i j))
    (rightAnnihilationN_creationN j i)
  split_ifs <;> simp [vacuumBoundary]

 theorem semicircularB_commutes_rightN (b : B) (i : N) :
    Commute (semicircularB (G := G) b) (rightSemicircularN i) := by
  have h : Commute (creationB (G := G) b) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftB_rightN b i)
  have hs := creationB_commutes_rightAnnihilationN (G := G) b i
  have hsl : Commute (star (creationB (G := G) b)) (rightCreationN i) := by
    simpa using hs.star_star
  exact (h.add_right hs).add_left (hsl.add_right h.star_star)

 theorem semicircularN_commutes_rightB (i : N) (b : B) :
    Commute (semicircularN (G := G) i) (rightSemicircularB b) := by
  have h : Commute (creationN (G := G) i) (rightCreationB b) :=
    LabelHilbert.lift_commute _ _ _ _ (leftN_rightB i b)
  have hs := creationN_commutes_rightAnnihilationB (G := G) i b
  have hsl : Commute (star (creationN (G := G) i)) (rightCreationB b) := by
    simpa using hs.star_star
  exact (h.add_right hs).add_left (hsl.add_right h.star_star)

 theorem semicircularB_commutes_rightG (b : B) (g : G) :
    Commute (semicircularB (N := N) b) (rightUnitaryG g) :=
  (creationB_commutes_rightUnitaryG b g).add_left (annihilationB_commutes_rightUnitaryG b g)

 theorem semicircularN_commutes_rightG (i : N) (g : G) :
    Commute (semicircularN (B := B) i) (rightUnitaryG g) :=
  (creationN_commutes_rightUnitaryG i g).add_left (annihilationN_commutes_rightUnitaryG i g)

 theorem unitaryG_commutes_rightB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (rightSemicircularB b) :=
  (unitaryG_commutes_rightCreationB g b).add_right (unitaryG_commutes_rightAnnihilationB g b)

 theorem unitaryG_commutes_rightN (g : G) (i : N) :
    Commute (unitaryG (B := B) g) (rightSemicircularN i) :=
  (unitaryG_commutes_rightCreationN g i).add_right (unitaryG_commutes_rightAnnihilationN g i)

abbrev Generator (B N G : Type) := B ⊕ N ⊕ G

def leftGenerator : Generator B N G → Space B N G →L[ℂ] Space B N G
  | .inl b => semicircularB b
  | .inr (.inl i) => semicircularN i
  | .inr (.inr g) => unitaryG g

def rightGenerator : Generator B N G → Space B N G →L[ℂ] Space B N G
  | .inl b => rightSemicircularB b
  | .inr (.inl i) => rightSemicircularN i
  | .inr (.inr g) => rightUnitaryG g

def inverseGenerator : Generator B N G → Generator B N G
  | .inl b => .inl b
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr g) => .inr (.inr g⁻¹)

@[simp] theorem star_leftGenerator (k : Generator B N G) :
    star (leftGenerator k) = leftGenerator (inverseGenerator k) := by
  rcases k with b | (i | g) <;> simp [leftGenerator, inverseGenerator]

@[simp] theorem star_rightGenerator (k : Generator B N G) :
    star (rightGenerator k) = rightGenerator (inverseGenerator k) := by
  rcases k with b | (i | g) <;> simp [rightGenerator, inverseGenerator]

 theorem generators_commute (j k : Generator B N G) :
    Commute (leftGenerator j) (rightGenerator k) := by
  rcases j with b | (i | g) <;> rcases k with c | (j | h)
  · exact semicircularB_commutes_rightB b c
  · exact semicircularB_commutes_rightN b j
  · exact semicircularB_commutes_rightG b h
  · exact semicircularN_commutes_rightB i c
  · exact semicircularN_commutes_rightN i j
  · exact semicircularN_commutes_rightG i h
  · exact unitaryG_commutes_rightB g c
  · exact unitaryG_commutes_rightN g j
  · exact unitaryG_commutes_rightUnitaryG g h

def algebra (B N G : Type) [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] :
    VonNeumannAlgebra (Space B N G) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (Set.range rightGenerator)
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

 theorem mem_algebra_iff (A : Space B N G →L[ℂ] Space B N G) :
    A ∈ algebra B N G ↔ ∀ k : Generator B N G, Commute A (rightGenerator k) := by
  change A ∈ StarSubalgebra.centralizer ℂ (Set.range rightGenerator) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h k
    exact (h _ ⟨k,rfl⟩).1.symm
  · rintro h _ ⟨k,rfl⟩
    exact ⟨(h k).eq.symm, by rw [star_rightGenerator]; exact (h _).eq.symm⟩

 theorem leftGenerator_mem (k : Generator B N G) : leftGenerator k ∈ algebra B N G :=
  (mem_algebra_iff _).mpr (generators_commute k)

def rightWick : Word B N G → Space B N G →L[ℂ] Space B N G
  | (([],g),[]) => rightUnitaryG g
  | (([b],g),t) => rightSemicircularB b * rightWick (([],g),t)
  | ((b::c::v,g),t) => rightSemicircularB b * rightWick ((c::v,g),t) -
      if b = c then rightWick ((v,g),t) else 0
  | (([],g),[(i,a)]) => rightUnitaryG g * (rightSemicircularN i * rightWick (a,[]))
  | (([],g),(i,a)::(j,d)::t) => rightUnitaryG g *
      (rightSemicircularN i * rightWick (a,(j,d)::t) -
        if a = ([],1) ∧ i = j then rightWick (d,t) else 0)
termination_by w => (w.2.length, w.1.1.length)

 theorem commute_rightWick (A : Space B N G →L[ℂ] Space B N G)
    (hA : ∀ k : Generator B N G, Commute A (rightGenerator k)) (w : Word B N G) :
    Commute A (rightWick w) := by
  induction w using rightWick.induct with
  | case1 g =>
    rw [rightWick]
    exact hA (.inr (.inr g))
  | case2 b g t ih =>
    rw [rightWick]
    exact (hA (.inl b)).mul_right ih
  | case3 b c v g t ih₁ ih₂ =>
    rw [rightWick]
    apply ((hA (.inl b)).mul_right ih₁).sub_right
    split_ifs
    · exact ih₂
    · exact Commute.zero_right A
  | case4 g i a ih =>
    rw [rightWick]
    exact (hA (.inr (.inr g))).mul_right ((hA (.inr (.inl i))).mul_right ih)
  | case5 g i a j d t ih₁ ih₂ =>
    rw [rightWick]
    apply (hA (.inr (.inr g))).mul_right
    apply ((hA (.inr (.inl i))).mul_right ih₁).sub_right
    split_ifs
    · exact ih₂
    · exact Commute.zero_right A

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
@[simp] theorem reverse_empty : reverse (B := B) (N := N) (G := G) empty = empty := by
  simp [empty, reverseAtom]

@[simp] theorem rightUnitaryG_basis_reverse (g : G) (w : Word B N G) :
    rightUnitaryG g (basis (reverse w)) = basis (reverse (leftG g w)) := by
  simp [basis, rightG]

 theorem rightSemicircularB_basis_reverse (b : B) (w : Word B N G) :
    rightSemicircularB b (basis (reverse w)) = basis (reverse (leftB b w)) +
      (removeB b w).elim 0 (fun a => basis (reverse a)) := by
  rw [rightSemicircularB, add_apply, basis, rightCreationB_single, rightAnnihilationB_single,
    reverse_involutive]
  simp only [rightB, reverse_involutive]
  cases removeB b w <;> rfl

 theorem rightSemicircularN_basis_reverse (i : N) (w : Word B N G) :
    rightSemicircularN i (basis (reverse w)) = basis (reverse (leftN i w)) +
      (removeN i w).elim 0 (fun a => basis (reverse a)) := by
  rw [rightSemicircularN, add_apply, basis, rightCreationN_single, rightAnnihilationN_single,
    reverse_involutive]
  simp only [rightN, reverse_involutive]
  cases removeN i w <;> rfl

@[simp] theorem rightWick_vacuum (w : Word B N G) :
    rightWick w (basis empty) = basis (reverse w) := by
  induction w using rightWick.induct with
  | case1 g => simp [rightWick, basis, empty, reverseAtom]
  | case2 b g t ih =>
    rw [rightWick, mul_apply_eq_comp, ih, rightSemicircularB_basis_reverse]
    simp [removeB, leftB]
  | case3 b c v g t ih₁ ih₂ =>
    rw [rightWick, sub_apply, mul_apply_eq_comp, ih₁, rightSemicircularB_basis_reverse]
    by_cases h : b = c <;> simp [h, removeB, leftB, ih₂]
  | case4 g i a ih =>
    rw [rightWick, mul_apply_eq_comp, mul_apply_eq_comp, ih,
      rightSemicircularN_basis_reverse]
    have h : removeN i (a, ([] : List (N × Atom B G))) = none := by
      simp only [removeN]; split <;> rfl
    simp [h, leftN, push, leftG]
  | case5 g i a j d t ih₁ ih₂ =>
    rw [rightWick, mul_apply_eq_comp, sub_apply, mul_apply_eq_comp, ih₁,
      rightSemicircularN_basis_reverse]
    by_cases ha : a = ([],1) <;> by_cases hij : i = j <;>
      simp [ha, hij, ih₂, removeN, leftN, push, leftG]

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
@[simp] theorem inverseGenerator_involutive (k : Generator B N G) :
    inverseGenerator (inverseGenerator k) = k := by
  rcases k with b | (i | g) <;> simp [inverseGenerator]

omit [Group G] in
 theorem semicircularB_basis (b : B) (w : Word B N G) :
    semicircularB b (basis w) = basis (leftB b w) + (removeB b w).elim 0 basis := by
  simp only [semicircularB, add_apply, basis, creationB_single, annihilationB_single]
  rfl

 theorem semicircularN_basis (i : N) (w : Word B N G) :
    semicircularN i (basis w) = basis (leftN i w) + (removeN i w).elim 0 basis := by
  simp only [semicircularN, add_apply, basis, creationN_single, annihilationN_single]
  rfl

@[simp] theorem unitaryG_basis (g : G) (w : Word B N G) :
    unitaryG g (basis w) = basis (leftG g w) := by simp [basis]

@[simp] theorem adjoint_rightGenerator_vacuum (k : Generator B N G) :
    star (rightGenerator k) (basis empty) = leftGenerator k (basis empty) := by
  rcases k with b | (i | g)
  · simp only [rightGenerator, leftGenerator, star_rightSemicircularB]
    simp [rightSemicircularB, semicircularB, basis, empty,
      annihilationB_single, removeB, leftB]
  · simp only [rightGenerator, leftGenerator, star_rightSemicircularN]
    simp [rightSemicircularN, semicircularN, basis, empty,
      annihilationN_single, removeN, leftN, append, push]
  · simp [rightGenerator, leftGenerator, basis, empty, leftG]

 theorem adjoint_right_mul_vacuum (A : Space B N G →L[ℂ] Space B N G)
    (h : ∀ j : Generator B N G, Commute (leftGenerator j) A) (k : Generator B N G) :
    star (rightGenerator k * A) (basis empty) = leftGenerator k (star A (basis empty)) := by
  have hc : Commute (leftGenerator k) (star A) := by
    simpa only [star_leftGenerator, inverseGenerator_involutive] using (h (inverseGenerator k)).star_star
  rw [star_mul, mul_apply_eq_comp, adjoint_rightGenerator_vacuum,
    ← mul_apply_eq_comp, hc.eq.symm, mul_apply_eq_comp]

 theorem adjoint_rightB_mul_vacuum (A : Space B N G →L[ℂ] Space B N G)
    (h : ∀ j : Generator B N G, Commute (leftGenerator j) A) (b : B) :
    star (rightSemicircularB (N := N) (G := G) b * A) (basis empty) = semicircularB b (star A (basis empty)) :=
  adjoint_right_mul_vacuum A h (.inl b)

 theorem adjoint_rightN_mul_vacuum (A : Space B N G →L[ℂ] Space B N G)
    (h : ∀ j : Generator B N G, Commute (leftGenerator j) A) (i : N) :
    star (rightSemicircularN (B := B) (G := G) i * A) (basis empty) = semicircularN i (star A (basis empty)) :=
  adjoint_right_mul_vacuum A h (.inr (.inl i))

 theorem adjoint_rightG_mul_vacuum (A : Space B N G →L[ℂ] Space B N G)
    (h : ∀ j : Generator B N G, Commute (leftGenerator j) A) (g : G) :
    star (rightUnitaryG (B := B) (N := N) g * A) (basis empty) = unitaryG g (star A (basis empty)) :=
  adjoint_right_mul_vacuum A h (.inr (.inr g))

 theorem rightWick_commutesLeft (w : Word B N G) (k : Generator B N G) :
    Commute (leftGenerator k) (rightWick w) :=
  commute_rightWick _ (generators_commute k) w

@[simp] theorem adjoint_rightWick_vacuum (w : Word B N G) :
    star (rightWick w) (basis empty) = basis w := by
  induction w using rightWick.induct with
  | case1 g => simp [rightWick, basis, empty]
  | case2 b g t ih =>
    rw [rightWick, adjoint_rightB_mul_vacuum (B := B) (N := N) (G := G) _ (rightWick_commutesLeft _) b, ih]
    simp [semicircularB_basis, removeB, leftB]
  | case3 b c v g t ih₁ ih₂ =>
    rw [rightWick, star_sub (R := Space B N G →L[ℂ] Space B N G) _ _, sub_apply,
      adjoint_rightB_mul_vacuum (B := B) (N := N) (G := G) _ (rightWick_commutesLeft _) b, ih₁]
    by_cases h : b = c <;> simp [h, ih₂, semicircularB_basis, removeB, leftB]
  | case4 g i a ih =>
    have hc (k : Generator B N G) : Commute (leftGenerator k)
        (rightSemicircularN i * rightWick (a, ([] : List (N × Atom B G)))) :=
      (generators_commute k (.inr (.inl i))).mul_right (rightWick_commutesLeft _ k)
    rw [rightWick, adjoint_rightG_mul_vacuum (B := B) (N := N) (G := G) _ hc g,
      adjoint_rightN_mul_vacuum (B := B) (N := N) (G := G) _ (rightWick_commutesLeft _) i, ih]
    have hn : removeN i (a, ([] : List (N × Atom B G))) = none := by
      simp only [removeN]; split <;> rfl
    simp [semicircularN_basis, hn, leftN, push, leftG]
  | case5 g i a j d t ih₁ ih₂ =>
    have hc (k : Generator B N G) : Commute (leftGenerator k)
        (rightSemicircularN i * rightWick (a,(j,d)::t) -
          if a = ([],1) ∧ i = j then rightWick (d,t) else 0) := by
      apply ((generators_commute k (.inr (.inl i))).mul_right (rightWick_commutesLeft _ k)).sub_right
      split_ifs
      · exact rightWick_commutesLeft _ k
      · exact Commute.zero_right _
    rw [rightWick, adjoint_rightG_mul_vacuum (B := B) (N := N) (G := G) _ hc g,
      star_sub (R := Space B N G →L[ℂ] Space B N G) _ _, sub_apply,
      adjoint_rightN_mul_vacuum (B := B) (N := N) (G := G) _ (rightWick_commutesLeft _) i, ih₁]
    by_cases ha : a = ([],1) <;> by_cases hij : i = j <;>
      simp [ha, hij, ih₂, semicircularN_basis, removeN, leftN, push, leftG]

theorem vacuum_separating (A : Space B N G →L[ℂ] Space B N G) (hA : A ∈ algebra B N G)
    (h0 : A (basis empty) = 0) : A = 0 := by
  have hsingle (w : Word B N G) : A (basis w) = 0 := by
    rw [← reverse_involutive w, ← rightWick_vacuum]
    rw [← mul_apply_eq_comp, (commute_rightWick A ((mem_algebra_iff A).mp hA) (reverse w)).eq,
      mul_apply_eq_comp, h0, map_zero]
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change A (lp.single 2 w z) = 0
  have hz : lp.single 2 w z = z • basis w := by simp [basis, ← lp.single_smul]
  rw [hz, map_smul, hsingle, smul_zero]

 theorem adjoint_vacuum_coefficient (A : Space B N G →L[ℂ] Space B N G)
    (hA : A ∈ algebra B N G) (w : Word B N G) :
    (star A (basis empty)) w = star ((A (basis empty)) (reverse w)) := by
  have hw : A (basis w) = rightWick (reverse w) (A (basis empty)) := by
    rw [← mul_apply_eq_comp,
      ← (commute_rightWick A ((mem_algebra_iff A).mp hA) (reverse w)).eq,
      mul_apply_eq_comp, rightWick_vacuum, reverse_involutive]
  calc
    (star A (basis empty)) w = inner ℂ (basis w) (star A (basis empty)) := by
      simp [basis, lp.inner_single_left]
    _ = inner ℂ (A (basis w)) (basis empty) := ContinuousLinearMap.adjoint_inner_right A _ _
    _ = inner ℂ (rightWick (reverse w) (A (basis empty))) (basis empty) := by rw [hw]
    _ = inner ℂ (A (basis empty)) (star (rightWick (reverse w)) (basis empty)) :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = star ((A (basis empty)) (reverse w)) := by
      rw [adjoint_rightWick_vacuum]
      simp [basis, lp.inner_single_right]

 theorem vacuum_product_formula (A D : Space B N G →L[ℂ] Space B N G)
    (hA : A ∈ algebra B N G) :
    inner ℂ (basis empty) ((A * D) (basis empty)) =
      ∑' w : Word B N G, (D (basis empty)) w * (A (basis empty)) (reverse w) := by
  rw [mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left A,
    ← ContinuousLinearMap.star_eq_adjoint, lp.inner_eq_tsum]
  apply tsum_congr
  intro w
  rw [RCLike.inner_apply, adjoint_vacuum_coefficient A hA w]
  simp

 theorem vacuum_tracial (A : Space B N G →L[ℂ] Space B N G) (hA : A ∈ algebra B N G)
    (D : Space B N G →L[ℂ] Space B N G) (hD : D ∈ algebra B N G) :
    inner ℂ (basis empty) ((A * D) (basis empty)) =
      inner ℂ (basis empty) ((D * A) (basis empty)) := by
  rw [vacuum_product_formula A D hA, vacuum_product_formula D A hD]
  let e : Word B N G ≃ Word B N G := ⟨reverse, reverse, reverse_involutive, reverse_involutive⟩
  calc
    (∑' w : Word B N G, (D (basis empty)) w * (A (basis empty)) (reverse w)) =
        ∑' w : Word B N G, (D (basis empty)) (reverse w) * (A (basis empty)) w := by
      simpa [e] using (e.tsum_eq (fun w : Word B N G =>
        (D (basis empty)) w * (A (basis empty)) (reverse w))).symm
    _ = _ := tsum_congr fun _ => mul_comm _ _

def tracialVector (B N G : Type) [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] :
    TracialVector (algebra B N G) where
  vacuum := basis empty
  norm_vacuum := by simp [basis, lp.norm_single (E := fun _ : Word B N G => ℂ) (p := 2)]
  tracial := vacuum_tracial
  separating := vacuum_separating

 theorem semicircularB_mem (b : B) : semicircularB (N := N) (G := G) b ∈ algebra B N G :=
  leftGenerator_mem (.inl b)
 theorem semicircularN_mem (i : N) : semicircularN (B := B) (G := G) i ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inl i))
 theorem unitaryG_mem (g : G) : unitaryG (B := B) (N := N) g ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inr g))

 theorem trace_unitaryG (g : G) :
    trace (tracialVector B N G) (unitaryG g) = if g = 1 then 1 else 0 := by
  change inner ℂ (basis empty) (unitaryG g (basis empty)) = _
  rw [unitaryG_basis]
  by_cases hg : g = 1 <;> simp [basis, leftG, empty, lp.inner_single_left, lp.single_apply, hg, eq_comm]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
