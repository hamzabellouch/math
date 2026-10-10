import OAI.Probability.CriticalZ3.LatticeGraph

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

structure Box where
  lower : Vertex
  upper : Vertex
  ordered : lower ≤ upper

namespace Box

@[ext] theorem ext {B C : Box} (hl : B.lower = C.lower) (hu : B.upper = C.upper) : B = C := by
  cases B; cases C; cases hl; cases hu; rfl

noncomputable def vertices (B : Box) : Finset Vertex := Finset.Icc B.lower B.upper

def Contains (B : Box) (x : Vertex) : Prop := ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i

@[simp] theorem mem_vertices (B : Box) (x : Vertex) : x ∈ B.vertices ↔ B.Contains x := by
  simp only [vertices, Finset.mem_Icc, Pi.le_def, Contains]
  exact ⟨fun h i => ⟨h.1 i,h.2 i⟩,fun h => ⟨fun i => (h i).1,fun i => (h i).2⟩⟩

noncomputable def bonds (B : Box) : Finset Bond :=
  (B.vertices ×ˢ Finset.univ).filter (fun e => B.Contains (step e.1 e.2))

@[simp] theorem mem_bonds (B : Box) (e : Bond) :
    e ∈ B.bonds ↔ B.Contains e.1 ∧ B.Contains (step e.1 e.2) := by
  simp [bonds]

def expand (B : Box) (j : ℕ) : Box where
  lower := fun i => B.lower i-j
  upper := fun i => B.upper i+j
  ordered := fun i => by
    have h : B.lower i ≤ B.upper i := B.ordered i
    dsimp
    omega

def cube (c : Vertex) (m : ℕ) : Box where
  lower := fun i => c i-m
  upper := fun i => c i+m
  ordered := fun i => by dsimp; omega

@[simp] theorem contains_cube (c x : Vertex) (m : ℕ) :
    (cube c m).Contains x ↔ ∀ i, |x i-c i| ≤ (m : ℤ) := by
  simp only [Contains,cube,abs_le]
  constructor <;> intro h i <;> have hi := h i <;> omega

theorem contains_expand (B : Box) (j : ℕ) {x : Vertex} (h : B.Contains x) :
    (B.expand j).Contains x := by
  intro i
  have hi := h i
  change B.lower i-j ≤ x i ∧ x i ≤ B.upper i+j
  omega

theorem expand_mono (B : Box) {j k : ℕ} (hjk : j ≤ k) {x : Vertex}
    (h : (B.expand j).Contains x) : (B.expand k).Contains x := by
  intro i
  have hi := h i
  change B.lower i-j ≤ x i ∧ x i ≤ B.upper i+j at hi
  change B.lower i-k ≤ x i ∧ x i ≤ B.upper i+k
  omega

@[simp] theorem expand_expand (B : Box) (j k : ℕ) : (B.expand j).expand k = B.expand (j+k) := by
  apply Box.ext <;> funext i <;> simp [expand] <;> omega

theorem neighbor_coordinates {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ i, |y i-x i| = 1 ∧ ∀ k, k ≠ i → y k = x k := by
  obtain ⟨i, h | h⟩ := h
  · subst y
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]
  · subst x
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]

theorem neighbor_distance {x y : Vertex} (h : NearestNeighbor x y) (i : Fin 3) :
    |y i-x i| ≤ 1 := by
  obtain ⟨k,hk,he⟩ := neighbor_coordinates h
  by_cases hik : i = k
  · simp [hik,hk]
  · simp [he i hik]

theorem neighbor_in_expand (B : Box) {x y : Vertex}
    (hx : B.Contains x) (hxy : NearestNeighbor x y) : (B.expand 1).Contains y := by
  intro i
  have hi := hx i
  have hd := neighbor_distance hxy i
  rw [abs_le] at hd
  change B.lower i-1 ≤ y i ∧ y i ≤ B.upper i+1
  omega

/-- The uniqueness used by the shell-closing argument, including corners. -/
theorem exterior_neighbor_unique (B : Box) {y z z' : Vertex}
    (hy : ¬ B.Contains y) (hz : B.Contains z) (hz' : B.Contains z')
    (hyz : NearestNeighbor y z) (hyz' : NearestNeighbor y z') : z = z' := by
  obtain ⟨i,hi⟩ : ∃ i, ¬ (B.lower i ≤ y i ∧ y i ≤ B.upper i) := by
    simpa only [Contains,not_forall] using hy
  obtain ⟨j,hj,hej⟩ := neighbor_coordinates hyz
  obtain ⟨k,hk,hek⟩ := neighbor_coordinates hyz'
  have hij : i = j := by
    by_contra h
    have hh := hej i h
    have hh' := hz i
    omega
  have hik : i = k := by
    by_contra h
    have hh := hek i h
    have hh' := hz' i
    omega
  subst j; subst k
  funext l
  by_cases hl : l = i
  · subst l
    have hz0 := hz i
    have hz1 := hz' i
    have hj0 := hj.le
    have hk0 := hk.le
    rw [abs_le] at hj0 hk0
    omega
  · rw [hej l hl,hek l hl]

def seedCenter (C : Box) (m : ℕ) (z : Vertex) : Vertex :=
  fun i => max (C.lower i+m) (min (C.upper i-m) (z i))

theorem seedCenter_bounds (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) (z : Vertex) (i : Fin 3) :
    C.lower i+m ≤ C.seedCenter m z i ∧ C.seedCenter m z i ≤ C.upper i-m := by
  exact ⟨le_max_left _ _,max_le (hw i) (min_le_left _ _)⟩

theorem seed_contained (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) (z : Vertex) :
    ∀ x, (cube (C.seedCenter m z) m).Contains x → C.Contains x := by
  intro x hx i
  have hb := C.seedCenter_bounds m hw z i
  have hx0 := (contains_cube _ _ _).mp hx i
  rw [abs_le] at hx0
  omega

theorem seed_contains_entry (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {z : Vertex} (hz : C.Contains z) :
    (cube (C.seedCenter m z) m).Contains z := by
  rw [contains_cube]
  intro i
  have hi := hz i
  have hwi := hw i
  dsimp [seedCenter]
  rw [abs_le]
  omega

theorem seed_center_near (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {z y : Vertex}
    (hz : C.Contains z) (hyz : NearestNeighbor y z) (i : Fin 3) :
    |C.seedCenter m z i-y i| ≤ (m : ℤ)+1 := by
  have h1 := (contains_cube _ _ _).mp (C.seed_contains_entry m hw hz) i
  have h2 := neighbor_distance hyz i
  rw [abs_le] at h1 h2 ⊢
  omega

theorem expanded_seed_width (B : Box) {m j : ℕ} (hmj : m ≤ j) (i : Fin 3) :
    (B.expand j).lower i+m ≤ (B.expand j).upper i-m := by
  have h : B.lower i ≤ B.upper i := B.ordered i
  dsimp [expand]
  omega

/-- The exact number of candidates excluded in one greedy selection. -/
theorem card_cube (c : Vertex) (m : ℕ) : (cube c m).vertices.card = (2*m+1)^3 := by
  rw [vertices,Pi.card_Icc]
  have he (i : Fin 3) : (Finset.Icc ((cube c m).lower i) ((cube c m).upper i)).card = 2*m+1 := by
    rw [Int.card_Icc]
    dsimp [cube]
    omega
  simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem disjoint_seeds {a b : Vertex} {m : ℕ}
    (h : ∃ i, (2*m : ℤ) < |a i-b i|) :
    Disjoint (cube a m).vertices (cube b m).vertices := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨i,hi⟩ := h
  have ha := (contains_cube _ _ _).mp ((mem_vertices _ _).mp hxa) i
  have hb := (contains_cube _ _ _).mp ((mem_vertices _ _).mp hxb) i
  rw [abs_le] at ha hb
  have hab : |a i-b i| ≤ 2*m := by rw [abs_le]; omega
  omega

theorem separated_subset (s : Finset Vertex) (m K : ℕ)
    (hcard : K*(8*m+5)^3 ≤ s.card) :
    ∃ t ⊆ s, t.card = K ∧
      ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ∃ i, (4*m+2 : ℤ) < |a i-b i| := by
  induction K generalizing s with
  | zero => exact ⟨∅,Finset.empty_subset s,rfl,by simp⟩
  | succ K ih =>
    have hcpos : 0 < (8*m+5)^3 := by positivity
    have hspos : 0 < s.card := by nlinarith
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hspos
    let U := (cube a (4*m+2)).vertices
    have hU : U.card = (8*m+5)^3 := by
      rw [card_cube]
      congr 1
      omega
    have hc : (s ∩ U).card ≤ (8*m+5)^3 := by
      rw [←hU]
      exact Finset.card_le_card Finset.inter_subset_right
    have hdiff : K*(8*m+5)^3 ≤ (s \ U).card := by
      have he := Finset.card_sdiff_add_card_inter s U
      rw [Nat.succ_mul] at hcard
      omega
    obtain ⟨t,ht,htc,hts⟩ := ih (s \ U) hdiff
    have hat : a ∉ t := by
      intro hat
      have haa := (Finset.mem_sdiff.mp (ht hat)).2
      apply haa
      apply (mem_vertices _ _).mpr
      rw [contains_cube]
      intro i
      simp only [sub_self,abs_zero]
      positivity
    have has (b : Vertex) (hb : b ∈ t) : ∃ i, (4*m+2 : ℤ) < |a i-b i| := by
      have hn := (Finset.mem_sdiff.mp (ht hb)).2
      have hn' : ¬ ∀ i, |b i-a i| ≤ (4*m+2 : ℤ) := by
        simpa [U,contains_cube] using hn
      push Not at hn'
      simpa only [abs_sub_comm] using hn'
    refine ⟨insert a t,?_,by simp [hat,htc],?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ha
      · exact (Finset.mem_sdiff.mp (ht hb)).1
    · intro b hb c hc hbc
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · exact (hbc rfl).elim
        · exact has c hc
      · rcases Finset.mem_insert.mp hc with hca | hc
        · subst c
          simpa only [abs_sub_comm] using has b hb
        · exact hts b hb c hc hbc

theorem separated_centers (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {y y' z z' : Vertex}
    (hz : C.Contains z) (hz' : C.Contains z')
    (hy : NearestNeighbor y z) (hy' : NearestNeighbor y' z')
    (hsep : ∃ i, (4*m+2 : ℤ) < |y i-y' i|) :
    ∃ i, (2*m : ℤ) < |C.seedCenter m z i-C.seedCenter m z' i| := by
  obtain ⟨i,hi⟩ := hsep
  refine ⟨i,?_⟩
  have h1 := C.seed_center_near m hw hz hy i
  have h2 := C.seed_center_near m hw hz' hy' i
  by_contra! hbad
  rw [abs_le] at h1 h2 hbad
  have hh : |y i-y' i| ≤ 4*m+2 := by rw [abs_le]; omega
  omega

def translateVertex (c x : Vertex) : Vertex := fun i => x i+c i

def translateBond (c : Vertex) (e : Bond) : Bond := (translateVertex c e.1,e.2)

theorem translateVertex_injective (c : Vertex) : Function.Injective (translateVertex c) := by
  intro x y h
  funext i
  have hi := congrFun h i
  dsimp [translateVertex] at hi
  omega

theorem translateBond_injective (c : Vertex) : Function.Injective (translateBond c) := by
  intro e e' h
  have h1 : e.1 = e'.1 := translateVertex_injective c (congrArg Prod.fst h)
  have h2 : e.2 = e'.2 := by simpa only [translateBond] using congrArg Prod.snd h
  exact Prod.ext h1 h2

@[simp] theorem step_translate (c x : Vertex) (i : Fin 3) :
    step (translateVertex c x) i = translateVertex c (step x i) := by
  funext j
  dsimp [step,translateVertex]
  omega

@[simp] theorem cube_contains_translate (c x : Vertex) (m : ℕ) :
    (cube c m).Contains (translateVertex c x) ↔ (cube 0 m).Contains x := by
  simp [contains_cube,translateVertex]

theorem cube_vertices_translate (c : Vertex) (m : ℕ) :
    (cube c m).vertices = (cube 0 m).vertices.image (translateVertex c) := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_image.mpr ⟨fun i => x i-c i,?_,?_⟩
    · rw [mem_vertices,contains_cube]
      simpa using (contains_cube _ _ _).mp ((mem_vertices _ _).mp hx)
    · funext i; simp [translateVertex]
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa [translateVertex] using hy

theorem cube_bonds_translate (c : Vertex) (m : ℕ) :
    (cube c m).bonds = (cube 0 m).bonds.image (translateBond c) := by
  ext e
  constructor
  · intro he
    let e' : Bond := (fun i => e.1 i-c i,e.2)
    have heq : translateBond c e' = e := by
      apply Prod.ext
      · funext i; simp [translateBond,translateVertex,e']
      · rfl
    refine Finset.mem_image.mpr ⟨e',?_,heq⟩
    rw [←heq,mem_bonds] at he
    simpa [translateBond,translateVertex] using he
  · intro he
    obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp he
    simpa [translateBond,translateVertex] using he'

theorem cube_bonds_card (c : Vertex) (m : ℕ) :
    (cube c m).bonds.card = (cube 0 m).bonds.card := by
  rw [cube_bonds_translate,Finset.card_image_of_injective _ (translateBond_injective c)]

def Within (B : Box) (x y : Vertex) : Prop :=
  NearestNeighbor x y ∧ B.Contains x ∧ B.Contains y

theorem within_symm (B : Box) {x y : Vertex} (h : B.Within x y) : B.Within y x := by
  obtain ⟨⟨i,hi⟩,hx,hy⟩ := h
  exact ⟨⟨i,hi.symm⟩,hy,hx⟩

theorem within_path_symm (B : Box) {x y : Vertex}
    (h : Relation.ReflTransGen B.Within x y) : Relation.ReflTransGen B.Within y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact .head (B.within_symm hab) ih

theorem line_step (x : Vertex) (i : Fin 3) (n : ℤ) :
    Function.update x i (n+1) = step (Function.update x i n) i := by
  funext j
  by_cases hj : j = i
  · subst j; simp [step]
  · simp [step,hj,Ne.symm hj]

theorem line_contains (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    (n : ℤ) (hn : B.lower i ≤ n ∧ n ≤ B.upper i) : B.Contains (Function.update x i n) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using hn
  · simpa [Function.update_of_ne hj] using hx j

theorem line_path_le (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    {a b : ℤ} (ha : B.lower i ≤ a) (hb : b ≤ B.upper i) (hab : a ≤ b) :
    Relation.ReflTransGen B.Within (Function.update x i a) (Function.update x i b) := by
  have hh (n : ℤ) (han : a ≤ n) : n ≤ b →
      Relation.ReflTransGen B.Within (Function.update x i a) (Function.update x i n) := by
    induction n,han using Int.leInduction with
    | base => intro _; exact .refl
    | succ n han ih =>
      intro hn
      apply (ih (by omega)).tail
      exact ⟨⟨i,Or.inl (line_step x i n)⟩,
        B.line_contains hx i n ⟨by omega,by omega⟩,
        B.line_contains hx i (n+1) ⟨by omega,by omega⟩⟩
  exact hh b hab le_rfl

theorem line_path (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    {b : ℤ} (hb : B.lower i ≤ b ∧ b ≤ B.upper i) :
    Relation.ReflTransGen B.Within x (Function.update x i b) := by
  have hx' := hx i
  by_cases h : x i ≤ b
  · simpa using B.line_path_le hx i hx'.1 hb.2 h
  · apply B.within_path_symm
    simpa using B.line_path_le hx i hb.1 hx'.2 (le_of_not_ge h)

/-- Every nonempty integer rectangle is nearest-neighbor connected internally. -/
theorem connected (B : Box) {x y : Vertex} (hx : B.Contains x) (hy : B.Contains y) :
    Relation.ReflTransGen B.Within x y := by
  let patch (s : Finset (Fin 3)) : Vertex := fun i => if i ∈ s then y i else x i
  have hp (s : Finset (Fin 3)) : B.Contains (patch s) := by
    intro i
    by_cases hi : i ∈ s
    · simpa [patch,hi] using hy i
    · simpa [patch,hi] using hx i
  have hc (s : Finset (Fin 3)) : Relation.ReflTransGen B.Within x (patch s) := by
    induction s using Finset.induction_on with
    | empty => simpa only [patch,Finset.notMem_empty,ite_false] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen B.Within x x)
    | @insert i s hi ih =>
      have he : patch (insert i s) = Function.update (patch s) i (y i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [patch]
        · simp [patch,hj]
      rw [he]
      exact ih.trans (B.line_path (hp s) i (hy i))
  simpa only [patch,Finset.mem_univ,ite_true] using hc Finset.univ

end Box
end CriticalZ3

end OAI
