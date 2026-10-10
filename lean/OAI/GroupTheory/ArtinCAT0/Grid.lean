import OAI.GroupTheory.ArtinCAT0.Winding

namespace OAI

namespace ArtinCAT0

/-- A triangular disk may have unpaired boundary darts. No topological theorem
is hidden in this interface: exactness is required and subsequently proved for
the explicit grid disks used in the controlled-diagram construction. -/
structure TrianglePatch (F V : Type*) where
  mate : Equiv.Perm (F × Fin 3)
  mate_involutive : Function.Involutive mate
  tail : F × Fin 3 → V
  tail_mate : ∀ d, mate d ≠ d → tail (mate d) = tail (d.1,d.2+1)

namespace TrianglePatch
variable {F V : Type*} (M : TrianglePatch F V)

def Boundary (d : F × Fin 3) : Prop := M.mate d = d

def Exact : Prop :=
  ∀ w : F × Fin 3 → ℝ,
    (∀ d, ¬ M.Boundary d → w (M.mate d) = -w d) →
    (∀ f, ∑ i : Fin 3, w (f,i) = 0) →
    ∃ p : V → ℝ, ∀ d, w d = p (M.tail (d.1,d.2+1)) - p (M.tail d)

@[simp] lemma mate_mate (d : F × Fin 3) : M.mate (M.mate d) = d := M.mate_involutive d

lemma tail_rotate_mate (d : F × Fin 3) (hd : ¬ M.Boundary d) :
    M.tail ((M.mate d).1,(M.mate d).2+1) = M.tail d := by
  rw [← M.tail_mate (M.mate d) (by intro h; exact hd (M.mate.injective h)), M.mate_mate]

end TrianglePatch

namespace GridDisk
variable (H N : ℕ) [NeZero N]

abbrev Face := (Fin (H+1) × Fin N × Bool) ⊕ Fin N
abbrev Vertex := (Fin (H+2) × Fin N) ⊕ Unit
abbrev A (r : Fin (H+1)) (i : Fin N) : Face H N := Sum.inl (r,i,false)
abbrev B (r : Fin (H+1)) (i : Fin N) : Face H N := Sum.inl (r,i,true)
abbrev C (i : Fin N) : Face H N := Sum.inr i

def mateFun : Face H N × Fin 3 → Face H N × Fin 3
  | (Sum.inl (r,i,false),k) =>
      if k = 0 then
        if h : r.val+1 < H+1 then (B H N ⟨r.val+1,h⟩ i,1) else (A H N r i,0)
      else if k = 1 then (B H N r (i+1),2) else (B H N r i,0)
  | (Sum.inl (r,i,true),k) =>
      if k = 0 then (A H N r i,2)
      else if k = 1 then
        if h : r.val = 0 then (C H N i,0) else (A H N ⟨r.val-1,by omega⟩ i,0)
      else (A H N r (i-1),1)
  | (Sum.inr i,k) =>
      if k = 0 then (B H N 0 i,1)
      else if k = 1 then (C H N (i+1),2) else (C H N (i-1),1)

lemma mateFun_involutive : Function.Involutive (mateFun H N) := by
  rintro ⟨f,k⟩
  rcases f with ⟨r,i,b⟩ | i
  · cases b <;> fin_cases k <;> simp only [mateFun]
    all_goals split_ifs <;> simp_all [A,B]
    all_goals split_ifs <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff, Fin.val_zero]
    all_goals try simp only [and_true]
    all_goals omega
  · fin_cases k <;> simp [mateFun,B,C]

def tail : Face H N × Fin 3 → Vertex H N
  | (Sum.inl (r,i,false),k) =>
      if k = 0 then Sum.inl (r.succ,i)
      else if k = 1 then Sum.inl (r.succ,i+1) else Sum.inl (r.castSucc,i+1)
  | (Sum.inl (r,i,true),k) =>
      if k = 0 then Sum.inl (r.succ,i)
      else if k = 1 then Sum.inl (r.castSucc,i+1) else Sum.inl (r.castSucc,i)
  | (Sum.inr i,k) =>
      if k = 0 then Sum.inl (0,i)
      else if k = 1 then Sum.inl (0,i+1) else Sum.inr ()

lemma tail_mateFun (d : Face H N × Fin 3) (hd : mateFun H N d ≠ d) :
    tail H N (mateFun H N d) = tail H N (d.1,d.2+1) := by
  rcases d with ⟨f,k⟩
  rcases f with ⟨r,i,b⟩ | i
  · cases b <;> fin_cases k <;> simp only [mateFun] at hd ⊢
    all_goals split_ifs at hd ⊢ <;> simp_all [tail,A,B,C,Fin.add_def]
    all_goals simp only [Fin.ext_iff,Fin.val_zero,Fin.val_succ,Fin.val_castSucc] at *
    all_goals omega
  · fin_cases k <;> simp [mateFun,tail,B,C,Fin.add_def]

def patch : TrianglePatch (Face H N) (Vertex H N) where
  mate := ⟨mateFun H N, mateFun H N, mateFun_involutive H N, mateFun_involutive H N⟩
  mate_involutive := mateFun_involutive H N
  tail := tail H N
  tail_mate := tail_mateFun H N

noncomputable def upper (w : Face H N × Fin 3 → ℝ) (r : Fin (H+1)) (i : Fin N) : ℝ :=
  if h : r.val = 0 then w (C H N i,0) else w (A H N ⟨r.val-1,by omega⟩ i,0)

noncomputable def potential (w : Face H N × Fin 3 → ℝ) : ℕ → Fin N → ℝ
  | 0,i => w (C H N i,2)
  | k+1,i => potential w k i + if h : k < H+1 then w (B H N ⟨k,h⟩ i,2) else 0

omit [NeZero N] in
lemma potential_succ (w : Face H N × Fin 3 → ℝ) (r : Fin (H+1)) (i : Fin N) :
    potential H N w (r.val+1) i = potential H N w r.val i + w (B H N r i,2) := by
  simp [potential,r.isLt]

lemma cocycle_relations (w : Face H N × Fin 3 → ℝ)
    (ha : ∀ d, ¬ (patch H N).Boundary d → w ((patch H N).mate d) = -w d) :
    (∀ r i, w (A H N r i,1) = -w (B H N r (i+1),2)) ∧
    (∀ r i, w (A H N r i,2) = -w (B H N r i,0)) ∧
    (∀ r i, w (B H N r i,1) = -upper H N w r i) ∧
    (∀ i, w (C H N i,1) = -w (C H N (i+1),2)) := by
  have hh (d) (hd : mateFun H N d ≠ d) : w (mateFun H N d) = -w d := ha d hd
  constructor
  · intro r i
    have h := hh (A H N r i,1) (by simp [mateFun,A,B])
    simp only [mateFun,A,B,Fin.isValue,Fin.reduceEq,ite_false,ite_true] at h
    linarith
  constructor
  · intro r i
    have h := hh (A H N r i,2) (by simp [mateFun,A,B])
    simp only [mateFun,A,B,Fin.isValue,Fin.reduceEq,ite_false] at h
    linarith
  constructor
  · intro r i
    have h := hh (B H N r i,1) (by simp [mateFun,A,B,C]; split_ifs <;> simp)
    by_cases hr : r.val = 0 <;> simp [mateFun,A,B,C,hr,upper] at h ⊢ <;> linarith
  · intro i
    have h := hh (C H N i,1) (by simp [mateFun,C])
    simp only [mateFun,C,Fin.isValue,Fin.reduceEq,ite_false,ite_true] at h
    linarith

/-- Exactness of the explicit capped cylindrical disk. The proof constructs a
potential by integrating vertically downward from the cap; the square and cap
relations verify every horizontal edge. -/
theorem exact : (patch H N).Exact := by
  intro w ha hc
  obtain ⟨hA₁,hA₂,hB₁,hC₁⟩ := cocycle_relations H N w ha
  have hc' (f) : w (f,0) + w (f,1) + w (f,2) = 0 := by
    simpa only [Fin.sum_univ_three] using hc f
  have hcap (i) : w (C H N i,0) = potential H N w 0 (i+1) - potential H N w 0 i := by
    have h := hc' (C H N i)
    rw [hC₁] at h
    simpa only [potential] using (show w (C H N i,0) = w (C H N (i+1),2)-w (C H N i,2) by linarith)
  have hstep (r : Fin (H+1))
      (hu : ∀ i, upper H N w r i = potential H N w r.val (i+1) - potential H N w r.val i) :
      ∀ i, w (A H N r i,0) = potential H N w (r.val+1) (i+1) - potential H N w (r.val+1) i := by
    intro i
    have hA := hc' (A H N r i)
    have hB := hc' (B H N r i)
    rw [hA₁,hA₂] at hA
    rw [hB₁,hu] at hB
    rw [potential_succ,potential_succ]
    linarith
  have hrow : ∀ k, ∀ hk : k < H+1, ∀ i,
      w (A H N ⟨k,hk⟩ i,0) = potential H N w (k+1) (i+1) - potential H N w (k+1) i := by
    intro k
    induction k with
    | zero =>
      intro hk
      apply hstep
      intro i
      simpa [upper] using hcap i
    | succ k ih =>
      intro hk
      apply hstep
      intro i
      simpa [upper] using ih (by omega) i
  have hu (r : Fin (H+1)) (i : Fin N) :
      upper H N w r i = potential H N w r.val (i+1) - potential H N w r.val i := by
    by_cases hr : r.val = 0
    · simpa [upper,hr] using hcap i
    · simpa [upper,hr,Nat.sub_add_cancel (by omega : 1 ≤ r.val)] using
        hrow (r.val-1) (by omega) i
  let p : Vertex H N → ℝ := fun v => match v with
    | Sum.inl (r,i) => potential H N w r.val i
    | Sum.inr _ => 0
  refine ⟨p, ?_⟩
  rintro ⟨f,k⟩
  change w (f,k) = p (tail H N (f,k+1)) - p (tail H N (f,k))
  rcases f with ⟨r,i,b⟩ | i
  · have hA := hc' (A H N r i)
    have hB := hc' (B H N r i)
    have hb₁ := hB₁ r i
    rw [hu] at hb₁
    have ha₁ := hA₁ r i
    have ha₂ := hA₂ r i
    have ha₀ := hrow r.val r.isLt i
    have hp := potential_succ H N w r i
    have hp' := potential_succ H N w r (i+1)
    cases b
    · fin_cases k
      · change w (A H N r i,0) = potential H N w (r.val+1) (i+1) - potential H N w (r.val+1) i
        exact ha₀
      · change w (A H N r i,1) = potential H N w r.val (i+1) - potential H N w (r.val+1) (i+1)
        linarith
      · change w (A H N r i,2) = potential H N w (r.val+1) i - potential H N w r.val (i+1)
        linarith
    · fin_cases k
      · change w (B H N r i,0) = potential H N w r.val (i+1) - potential H N w (r.val+1) i
        linarith
      · change w (B H N r i,1) = potential H N w r.val i - potential H N w r.val (i+1)
        linarith
      · change w (B H N r i,2) = potential H N w (r.val+1) i - potential H N w r.val i
        linarith
  · have h₀ := hcap i
    have h₁ := hC₁ i
    fin_cases k
    · change w (C H N i,0) = potential H N w 0 (i+1) - potential H N w 0 i
      exact h₀
    · change w (C H N i,1) = 0 - w (C H N (i+1),2)
      simpa using h₁
    · change w (C H N i,2) = w (C H N i,2) - 0
      ring

end GridDisk
end ArtinCAT0

namespace ArtinCAT0

namespace TrianglePatch
variable {A U : Type*}

/-- Three marked, equally subdivided sides of a triangular patch. The marks
are combinatorial; the vertices and faces need not be mapped injectively. -/
structure Sides (P : TrianglePatch A U) (K : ℕ) where
  dart : Fin 3 × Fin K → A × Fin 3
  point : Fin 3 × Fin (K+1) → U
  dart_injective : Function.Injective dart
  fixed : ∀ e, P.Boundary (dart e)
  complete : ∀ d, P.Boundary d → ∃ e, dart e = d
  tail : ∀ i j, P.tail (dart (i,j)) = point (i,j.castSucc)
  head : ∀ i j, P.tail ((dart (i,j)).1,(dart (i,j)).2+1) = point (i,j.succ)
  ends : ∀ i, point (i,Fin.last K) = point (i+1,0)

lemma boundary_mate (P : TrianglePatch A U) (d : A × Fin 3) :
    P.Boundary (P.mate d) ↔ P.Boundary d := by
  unfold Boundary
  rw [P.mate_mate]
  exact eq_comm

namespace Sides
variable {P : TrianglePatch A U} {K : ℕ} [NeZero K] (S : P.Sides K)
noncomputable def index (d : A × Fin 3) : Fin 3 × Fin K := by
  classical
  exact if h : P.Boundary d then (S.complete d h).choose else (0,0)

@[simp] lemma index_dart (e : Fin 3 × Fin K) : S.index (S.dart e) = e := by
  classical
  apply S.dart_injective
  simp only [index,dite_eq_left (S.fixed e)]
  exact (S.complete _ (S.fixed e)).choose_spec

lemma dart_index (d : A × Fin 3) (h : P.Boundary d) : S.dart (S.index d) = d := by
  classical
  simp only [index,dite_eq_left h]
  exact (S.complete d h).choose_spec

end Sides
end TrianglePatch

lemma reverse_chain_difference {K : ℕ} (a b : Fin (K+1) → ℝ)
    (h : ∀ j : Fin K, a j.succ - a j.castSucc = b j.rev.castSucc - b j.rev.succ) :
    ∀ j, a j - a 0 = b j.rev - b (Fin.last K) := by
  intro j
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    have hh := h j
    rw [Fin.rev_castSucc] at ih
    rw [Fin.rev_succ]
    linarith

namespace TriangleMesh
variable {F V A U : Type*} (M : TriangleMesh F V) (P : TrianglePatch A U)
  {K : ℕ} [NeZero K] (S : P.Sides K)

namespace Replacement

noncomputable def mateFun (d : (F × A) × Fin 3) : (F × A) × Fin 3 := by
  classical
  exact if h : P.Boundary (d.1.2,d.2) then
    let e := S.index (d.1.2,d.2)
    let m := M.mate (d.1.1,e.1)
    let t := S.dart (m.2,e.2.rev)
    ((m.1,t.1),t.2)
  else
    let t := P.mate (d.1.2,d.2)
    ((d.1.1,t.1),t.2)

@[simp] lemma mate_boundary (f : F) (i : Fin 3) (j : Fin K) :
    mateFun M P S ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) =
      (((M.mate (f,i)).1, (S.dart ((M.mate (f,i)).2,j.rev)).1),
        (S.dart ((M.mate (f,i)).2,j.rev)).2) := by
  classical
  simp only [mateFun,Prod.mk.eta,S.fixed,dite_eq_left,S.index_dart]

lemma mate_internal (f : F) (d : A × Fin 3) (hd : ¬ P.Boundary d) :
    mateFun M P S ((f,d.1),d.2) = ((f,(P.mate d).1),(P.mate d).2) := by
  classical
  simp [mateFun,hd]

lemma mateFun_involutive : Function.Involutive (mateFun M P S) := by
  rintro ⟨⟨f,a⟩,k⟩
  by_cases hd : P.Boundary (a,k)
  · obtain ⟨⟨i,j⟩,he⟩ := S.complete _ hd
    have hd' : ((f,a),k) = ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) := by rw [he]
    rw [hd',mate_boundary,mate_boundary,M.mate_mate,Fin.rev_rev]
  · rw [mate_internal M P S f (a,k) hd,
      mate_internal M P S f (P.mate (a,k)) (by simpa only [P.boundary_mate] using hd),
      P.mate_mate]

lemma mateFun_ne (d : (F × A) × Fin 3) : mateFun M P S d ≠ d := by
  rcases d with ⟨⟨f,a⟩,k⟩
  by_cases hd : P.Boundary (a,k)
  · obtain ⟨⟨i,j⟩,he⟩ := S.complete _ hd
    have hd' : ((f,a),k) = ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) := by rw [he]
    rw [hd',mate_boundary]
    intro h
    have hface := congrArg (fun d : (F×A)×Fin 3 => d.1.1) h
    have hdart := congrArg (fun d : (F×A)×Fin 3 => (d.1.2,d.2)) h
    dsimp only at hdart hface
    have hi := congrArg Prod.fst (S.dart_injective hdart)
    exact M.mate_ne (f,i) (Prod.ext hface hi)
  · rw [mate_internal M P S f (a,k) hd]
    intro h
    apply hd
    exact congrArg (fun d : (F×A)×Fin 3 => (d.1.2,d.2)) h

/-- Boundary vertices glued with opposite side parametrizations. -/
def Seam (u v : F × U) : Prop :=
  ∃ f i j, u = (f,S.point (i,j)) ∧
    v = ((M.mate (f,i)).1,S.point ((M.mate (f,i)).2,j.rev))

abbrev Vertex := Quot (Seam M P S)

def vertex (x : F × U) : Vertex M P S := Quot.mk _ x

omit [NeZero K] in
lemma vertex_seam (f : F) (i : Fin 3) (j : Fin (K+1)) :
    vertex M P S (f,S.point (i,j)) =
      vertex M P S ((M.mate (f,i)).1,S.point ((M.mate (f,i)).2,j.rev)) :=
  Quot.sound ⟨f,i,j,rfl,rfl⟩

def tail (d : (F × A) × Fin 3) : Vertex M P S :=
  vertex M P S (d.1.1,P.tail (d.1.2,d.2))

lemma tail_mateFun (d : (F × A) × Fin 3) :
    tail M P S (mateFun M P S d) = tail M P S (d.1,d.2+1) := by
  rcases d with ⟨⟨f,a⟩,k⟩
  by_cases hd : P.Boundary (a,k)
  · obtain ⟨⟨i,j⟩,he⟩ := S.complete _ hd
    have hd' : ((f,a),k) = ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) := by rw [he]
    rw [hd',mate_boundary]
    change vertex M P S ((M.mate (f,i)).1,P.tail (S.dart ((M.mate (f,i)).2,j.rev))) =
      vertex M P S (f,P.tail ((S.dart (i,j)).1,(S.dart (i,j)).2+1))
    rw [S.tail,S.head,vertex_seam M P S f i j.succ,Fin.rev_succ]
  · rw [mate_internal M P S f (a,k) hd]
    change vertex M P S (f,P.tail (P.mate (a,k))) = vertex M P S (f,P.tail (a,k+1))
    rw [P.tail_mate _ hd]

noncomputable def mesh : TriangleMesh (F × A) (Vertex M P S) where
  mate := ⟨mateFun M P S,mateFun M P S,mateFun_involutive M P S,mateFun_involutive M P S⟩
  mate_involutive := mateFun_involutive M P S
  mate_ne := mateFun_ne M P S
  tail := tail M P S
  tail_mate := tail_mateFun M P S

/-- Substituting an exact triangular patch in every coarse face preserves
exactness. This is a cochain proof, independent of any triangulation theorem. -/
theorem exact (hM : M.Exact) (hP : P.Exact) : (mesh M P S).Exact := by
  classical
  intro w ha hc
  have hf (f : F) : ∃ p : U → ℝ, ∀ d : A × Fin 3,
      w ((f,d.1),d.2) = p (P.tail (d.1,d.2+1)) - p (P.tail d) := by
    apply hP
    · intro d hd
      have h := ha ((f,d.1),d.2)
      change w (mateFun M P S ((f,d.1),d.2)) = -w ((f,d.1),d.2) at h
      rwa [mate_internal M P S f d hd] at h
    · intro a
      exact hc (f,a)
  choose p hp using hf
  let b (f : F) (i : Fin 3) (j : Fin (K+1)) := p f (S.point (i,j))
  have hb (f : F) (i : Fin 3) (j : Fin K) :
      w ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) = b f i j.succ - b f i j.castSucc := by
    simpa only [b,S.head,S.tail] using hp f (S.dart (i,j))
  have hpair (f : F) (i : Fin 3) (j : Fin (K+1)) :
      b f i j - b f i 0 = b (M.mate (f,i)).1 (M.mate (f,i)).2 j.rev -
        b (M.mate (f,i)).1 (M.mate (f,i)).2 (Fin.last K) := by
    apply reverse_chain_difference
    intro j
    have h := ha ((f,(S.dart (i,j)).1),(S.dart (i,j)).2)
    change w (mateFun M P S _) = -w _ at h
    rw [mate_boundary,hb,hb] at h
    linarith
  let W (d : F × Fin 3) := b d.1 d.2 (Fin.last K) - b d.1 d.2 0
  have hWa (d : F × Fin 3) : W (M.mate d) = -W d := by
    have h := hpair d.1 d.2 (Fin.last K)
    simp only [Fin.rev_last] at h
    dsimp only [W]
    linarith
  have hWc (f : F) : ∑ i : Fin 3, W (f,i) = 0 := by
    simp only [W,b,S.ends,Fin.sum_univ_three]
    change (p f (S.point (1,0)) - p f (S.point (0,0))) +
      (p f (S.point (2,0)) - p f (S.point (1,0))) +
      (p f (S.point (0,0)) - p f (S.point (2,0))) = 0
    ring
  obtain ⟨q,hq⟩ := hM W hWa hWc
  have hcorner (f : F) (i : Fin 3) :
      b f i 0 - b f 0 0 = q (M.tail (f,i)) - q (M.tail (f,0)) := by
    have h₀ := hq (f,0)
    have h₁ := hq (f,1)
    simp only [W,b,S.ends] at h₀ h₁
    change p f (S.point (1,0)) - p f (S.point (0,0)) =
      q (M.tail (f,1)) - q (M.tail (f,0)) at h₀
    change p f (S.point (2,0)) - p f (S.point (1,0)) =
      q (M.tail (f,2)) - q (M.tail (f,1)) at h₁
    fin_cases i
    · simp [b]
    · exact h₀
    · change p f (S.point (2,0)) - p f (S.point (0,0)) =
        q (M.tail (f,2)) - q (M.tail (f,0))
      linarith
  let z (v : F × U) := p v.1 v.2 - b v.1 0 0 + q (M.tail (v.1,0))
  have hz {u v : F × U} (h : Seam M P S u v) : z u = z v := by
    obtain ⟨f,i,j,rfl,rfl⟩ := h
    have h₁ := hpair f i j
    have h₂ := hcorner f i
    have h₃ := hcorner (M.mate (f,i)).1 (M.mate (f,i)).2
    have h₄ := hq (M.mate (f,i))
    rw [M.tail_rotate_mate] at h₄
    dsimp only [W] at h₄
    change (b f i j - b f 0 0 + q (M.tail (f,0))) =
      b (M.mate (f,i)).1 (M.mate (f,i)).2 j.rev - b (M.mate (f,i)).1 0 0 +
        q (M.tail ((M.mate (f,i)).1,0))
    linarith
  refine ⟨Quot.lift z (fun _ _ h => hz h),?_⟩
  rintro ⟨⟨f,a⟩,k⟩
  change w ((f,a),k) = z (f,P.tail (a,k+1)) - z (f,P.tail (a,k))
  dsimp only [z]
  rw [hp f (a,k)]
  ring

end Replacement
end TriangleMesh
end ArtinCAT0

namespace ArtinCAT0.GridDisk
variable (H N : ℕ) [NeZero N]

lemma boundary_iff (d : Face H N × Fin 3) :
    (patch H N).Boundary d ↔ ∃ i, d = (A H N (Fin.last H) i,0) := by
  change mateFun H N d = d ↔ _
  rcases d with ⟨f,k⟩
  rcases f with ⟨r,i,b⟩ | i
  · cases b
    · fin_cases k
      · change (if h : r.val+1 < H+1 then (B H N ⟨r.val+1,h⟩ i,1)
          else (A H N r i,0)) = (A H N r i,0) ↔ _
        split_ifs with h
        · have hr : r ≠ Fin.last H := by
            intro he
            have := congrArg Fin.val he
            change r.val = H at this
            omega
          simp [A,B,hr]
        · have hr : r = Fin.last H := by
            apply Fin.ext
            change r.val = H
            have := r.isLt
            omega
          subst r
          simp
      · norm_num [mateFun,A,B]
      · norm_num [mateFun,A,B]
    · fin_cases k
      · norm_num [mateFun,A,B]
      · change (if h : r.val = 0 then (C H N i,0)
          else (A H N ⟨r.val-1,by omega⟩ i,0)) = (B H N r i,1) ↔ _
        split_ifs <;> simp [A,B,C]
      · norm_num [mateFun,A,B]
  · fin_cases k <;> norm_num [mateFun,A,B,C]

variable (K : ℕ) [NeZero K]

def sideIndex (i : Fin 3) (j : Fin (K+1)) : Fin (3*K) :=
  ⟨(i.val*K+j.val) % (3*K),Nat.mod_lt _ (Nat.mul_pos (by decide) (NeZero.pos K))⟩

def sideDart (e : Fin 3 × Fin K) : Face H (3*K) × Fin 3 :=
  (A H (3*K) (Fin.last H) (finProdFinEquiv e),0)

def sidePoint (e : Fin 3 × Fin (K+1)) : Vertex H (3*K) :=
  Sum.inl (Fin.last (H+1),sideIndex K e.1 e.2)

lemma sideIndex_castSucc (i : Fin 3) (j : Fin K) :
    sideIndex K i j.castSucc = finProdFinEquiv (i,j) := by
  apply Fin.ext
  change (i.val*K+j.val) % (3*K) = j.val + K*i.val
  rw [Nat.mul_comm i.val K, Nat.add_comm]
  exact Nat.mod_eq_of_lt (finProdFinEquiv (i,j)).isLt

lemma sideIndex_succ (i : Fin 3) (j : Fin K) :
    sideIndex K i j.succ = finProdFinEquiv (i,j) + 1 := by
  apply Fin.ext
  change (i.val*K+(j.val+1)) % (3*K) = ((j.val+K*i.val)+(1 % (3*K))) % (3*K)
  rw [Nat.mod_eq_of_lt (show 1 < 3*K by have := NeZero.pos K; omega)]
  congr 1
  ring

lemma sidePoint_ends (i : Fin 3) :
    sidePoint H K (i,Fin.last K) = sidePoint H K (i+1,0) := by
  apply congrArg Sum.inl
  congr 1
  apply Fin.ext
  fin_cases i
  · change (0*K+K) % (3*K) = (1*K+0) % (3*K)
    simp
  · change (1*K+K) % (3*K) = (2*K+0) % (3*K)
    congr 1; ring
  · change (2*K+K) % (3*K) = (0*K+0) % (3*K)
    rw [show 2*K+K = 3*K by omega]
    simp

noncomputable def sides : (patch H (3*K)).Sides K where
  dart := sideDart H K
  point := sidePoint H K
  dart_injective := by
    intro e e' h
    apply finProdFinEquiv.injective
    simpa only [sideDart,A,Prod.mk.injEq,Sum.inl.injEq,true_and,and_true] using h
  fixed := by
    intro ⟨i,j⟩
    exact (boundary_iff H (3*K) _).2 ⟨_,rfl⟩
  complete := by
    intro d hd
    obtain ⟨i,rfl⟩ := (boundary_iff H (3*K) d).1 hd
    refine ⟨finProdFinEquiv.symm i,?_⟩
    change (A H (3*K) (Fin.last H) (finProdFinEquiv (finProdFinEquiv.symm i)),0) = _
    rw [Equiv.apply_symm_apply]
  tail := by
    intro i j
    change Sum.inl ((Fin.last H).succ,finProdFinEquiv (i,j)) =
      Sum.inl (Fin.last (H+1),sideIndex K i j.castSucc)
    rw [sideIndex_castSucc]
    rfl
  head := by
    intro i j
    change Sum.inl ((Fin.last H).succ,finProdFinEquiv (i,j)+1) =
      Sum.inl (Fin.last (H+1),sideIndex K i j.succ)
    rw [sideIndex_succ]
    rfl
  ends := sidePoint_ends H K

end ArtinCAT0.GridDisk

namespace ArtinCAT0.TriangleMesh

/-- The sphere consisting of two oppositely oriented triangles. -/
def doubleTriangle : TriangleMesh Bool (Fin 3) where
  mate := (show Function.Involutive (fun d : Bool × Fin 3 => (!d.1,-d.2-1)) from
    fun d => by rcases d with ⟨b,i⟩; simp).toPerm
  mate_involutive := by rintro ⟨b,i⟩; simp
  mate_ne := by rintro ⟨b,i⟩ h; have := congrArg Prod.fst h; cases b <;> simp at this
  tail := fun d => if d.1 then -d.2 else d.2
  tail_mate := by rintro ⟨b,i⟩; cases b <;> simp <;> abel

lemma doubleTriangle_exact : doubleTriangle.Exact := by
  intro w hw hf
  let p : Fin 3 → ℝ := fun i => if i = 0 then 0 else if i = 1 then w (false,0)
    else w (false,0)+w (false,1)
  have hs : w (false,0)+w (false,1)+w (false,2) = 0 := by
    simpa only [Fin.sum_univ_three,add_assoc] using hf false
  have he (i : Fin 3) : w (false,i) = p (i+1)-p i := by
    fin_cases i
    · change w (false,0) = p 1-p 0
      simp [p]
    · change w (false,1) = p 2-p 1
      simp [p,show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide]
    · change w (false,2) = p 0-p 2
      simp [p,show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide]
      linarith
  refine ⟨p,?_⟩
  rintro ⟨b,i⟩
  cases b
  · exact he i
  · have hm := hw (false,-i-1)
    change w (true,-(-i-1)-1) = -w (false,-i-1) at hm
    rw [show -(-i-1)-1 = i by abel,he] at hm
    change w (true,i) = p (-(i+1))-p (-i)
    rw [hm,show -i-1+1 = -i by abel,show -i-1 = -(i+1) by abel]
    ring

end ArtinCAT0.TriangleMesh

end OAI
