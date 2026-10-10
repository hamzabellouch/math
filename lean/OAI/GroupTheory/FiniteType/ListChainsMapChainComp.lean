import Mathlib
import OAI.GroupTheory.FiniteType.ListChainsHasPropagation

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*)

@[simp] lemma mapChain_comp {H K : Type*} (f : G → H) (g : H → K) (c : Chain G) :
    mapChain H g (mapChain G f c) = mapChain G (g ∘ f) c := by
  have h : mapChain H g ∘ₗ mapChain G f = mapChain G (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro s r
    simp [List.map_map]
  exact LinearMap.congr_fun h c

@[simp] lemma mapChain_id (c : Chain G) : mapChain G id c = c := by
  have h : mapChain G id = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  exact LinearMap.congr_fun h c

variable [Group G]

def FillsAt (B : Set G) (n : ℕ) (z : Chain G) : Prop :=
  ∃ w, w ∈ degreeModule G (n+1) ∧ w ∈ controlledModule G B ∧ boundary G w = z

lemma FillsAt.mono {A B : Set G} {n : ℕ} {z : Chain G}
    (hz : FillsAt G A n z) (hAB : A ⊆ B) : FillsAt G B n z := by
  obtain ⟨w,hw,ha,hd⟩ := hz
  exact ⟨w,hw,controlledModule_mono G hAB ha,hd⟩

lemma FillsAt.add {B : Set G} {n : ℕ} {z z' : Chain G}
    (hz : FillsAt G B n z) (hz' : FillsAt G B n z') : FillsAt G B n (z+z') := by
  obtain ⟨w,hw,ha,hd⟩ := hz
  obtain ⟨w',hw',ha',hd'⟩ := hz'
  exact ⟨w+w',Submodule.add_mem _ hw hw',Submodule.add_mem _ ha ha',by rw [map_add,hd,hd']⟩

lemma FillsAt.neg {B : Set G} {n : ℕ} {z : Chain G}
    (hz : FillsAt G B n z) : FillsAt G B n (-z) := by
  obtain ⟨w,hw,ha,hd⟩ := hz
  exact ⟨-w,Submodule.neg_mem _ hw,Submodule.neg_mem _ ha,by rw [map_neg,hd]⟩

lemma FillsAt.map {H : Type*} [Group H] {B : Set G} {n : ℕ} {z : Chain G}
    (hz : FillsAt G B n z) (f : G →* H) : FillsAt H (f '' B) n (mapChain G f z) := by
  obtain ⟨w,hw,ha,hd⟩ := hz
  exact ⟨mapChain G f w,mapChain_mem_degree G f hw,mapChain_mem_controlled G H f ha,
    by rw [boundary_mapChain,hd]⟩

theorem controlled_commuting_additivity (f : G →* G) (J : Chain G →ₗ[ℤ] Chain G)
    {n : ℕ} (hn : 0 < n) {A C : Set G} (hA : IsBound G A) (hC : IsBound G C)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    (hJzero : ∀ c, c ∈ degreeModule G n → J c = 0)
    (hJcontrol : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G C)
    (hJlower : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
      boundary G (J c) + J (boundary G c) = mapChain G f c - K G 1 c)
    (h₁ h₂ : G →* G) (comm : ∀ x y, Commute (h₁ x) (h₂ y)) :
    ∃ B : Set G, IsBound G B ∧
      ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
        FillsAt G B n (mapChain G (fun x => h₁ (f x) * h₂ (f x)) z -
          mapChain G (h₁ ∘ f) z - mapChain G (h₂ ∘ f) z) := by
  obtain ⟨B,hB,hfill⟩ := controlled_product_additivity G f J hn hA hC
    hJdeg hJzero hJcontrol hJlower
  let μ := h₁.noncommCoprod h₂ comm
  refine ⟨μ '' B,hB.image (G × G) μ,?_⟩
  intro z hzd hza hz
  obtain ⟨w,hwd,hwb,hw⟩ := hfill z hzd hza hz
  refine ⟨mapChain (G × G) μ w,mapChain_mem_degree (G × G) μ hwd,
    mapChain_mem_controlled (G × G) G μ hwb,?_⟩
  rw [boundary_mapChain,hw,map_sub,map_sub]
  simp only [mapChain_comp,Function.comp_def,μ,MonoidHom.noncommCoprod_apply,map_one,
    one_mul,mul_one]
  abel

open scoped Pointwise

def symmetricClosure (S : Set G) : Set G := insert 1 (S ∪ S⁻¹)

lemma subset_symmetricClosure (S : Set G) : S ⊆ symmetricClosure G S :=
  fun _ h => Set.mem_insert_of_mem _ (Or.inl h)

lemma isBound_symmetricClosure {S : Set G} (hS : S.Finite) :
    IsBound G (symmetricClosure G S) where
  finite := (hS.union hS.inv).insert 1
  one_mem := Set.mem_insert _ _
  inv_mem := by
    intro a ha
    rcases ha with rfl | ha | ha
    · simpa only [symmetricClosure,inv_one] using (Set.mem_insert (1 : G) (S ∪ S⁻¹))
    · exact Set.mem_insert_of_mem _ (Or.inr (by simpa using ha))
    · exact Set.mem_insert_of_mem _ (Or.inl ha)

lemma finite_common_bound {ι : Type*} [Finite ι] (B : ι → Set G)
    (hB : ∀ i, IsBound G (B i)) :
    ∃ C : Set G, IsBound G C ∧ ∀ i, B i ⊆ C := by
  let C := symmetricClosure G (⋃ i, B i)
  refine ⟨C,isBound_symmetricClosure G (Set.finite_iUnion fun i => (hB i).finite),?_⟩
  intro i
  exact Set.Subset.trans (Set.subset_iUnion B i) (subset_symmetricClosure G _)

end

section

variable (G : Type*) [Group G]

lemma mapChain_mem_controlled_of_differences {H : Type*} [Group H] (f : G → H)
    {A : Set G} {B : Set H}
    (hf : ∀ x y, x⁻¹*y ∈ A → (f x)⁻¹*f y ∈ B)
    {c : Chain G} (hc : c ∈ controlledModule G A) :
    mapChain G f c ∈ controlledModule H B := by
  apply BasedComplex.map_mem_of_support (mapChain G f) _ c
  intro s hs
  refine vertexModule_le_controlledModule H (V := f '' vertices G s) ?_
    (mapChain_mem_vertices G f (V := vertices G s) (W := f '' vertices G s)
      (fun x hx => ⟨x,hx,rfl⟩) (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1))
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact hf x y (hc hs x hx y hy)

lemma leftTranslate_mem_controlled (a : G) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) :
    mapChain G (fun x => a*x) c ∈ controlledModule G A := by
  apply mapChain_mem_controlled_of_differences G _ _ hc
  intro x y h
  simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using h

def pathSubgroup (A : Set G) : Subgroup G where
  carrier := {g | FillsAt G A 0 (vertex G g - vertex G 1)}
  one_mem' := ⟨0,Submodule.zero_mem _,Submodule.zero_mem _,by simp⟩
  mul_mem' := by
    rintro g h ⟨c,hcd,hc,dc⟩ ⟨d,hdd,hd,dd⟩
    refine ⟨c + mapChain G (fun x => g*x) d,
      Submodule.add_mem _ hcd (mapChain_mem_degree G _ hdd),
      Submodule.add_mem _ hc (leftTranslate_mem_controlled G g hd),?_⟩
    rw [map_add,dc,boundary_mapChain,dd,map_sub,mapChain_vertex,mapChain_vertex,mul_one]
    abel
  inv_mem' := by
    rintro g ⟨c,hcd,hc,dc⟩
    refine ⟨-mapChain G (fun x => g⁻¹*x) c,
      Submodule.neg_mem _ (mapChain_mem_degree G _ hcd),
      Submodule.neg_mem _ (leftTranslate_mem_controlled G g⁻¹ hc),?_⟩
    rw [map_neg,boundary_mapChain,dc,map_sub,mapChain_vertex,mapChain_vertex,
      inv_mul_cancel,mul_one]
    abel

lemma mem_pathSubgroup_of_mem {A : Set G} (h1 : (1 : G) ∈ A) {g : G}
    (hg : g ∈ A) (hgi : g⁻¹ ∈ A) : g ∈ pathSubgroup G A := by
  refine ⟨cone G 1 (vertex G g),cone_mem_degreeModule G 1 (vertex_mem_degreeModule G g),?_,?_⟩
  · refine vertexModule_le_controlledModule G (V := {1,g}) ?_
      (cone_mem_vertexModule G (Set.mem_insert _ _)
        (vertex_mem_vertexModule G (Set.mem_insert_of_mem _ rfl)))
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simpa only [inv_one,one_mul] using h1
    · simpa only [inv_one,one_mul] using hg
    · simpa only [mul_one] using hgi
    · simpa only [inv_mul_cancel] using h1
  · rw [boundary_cone,boundary_vertex,map_zero,sub_zero,K_apply,augmentation_vertex,one_smul]

lemma path_of_mem_closure {A : Set G} (hA : IsBound G A) {g : G}
    (hg : g ∈ Subgroup.closure A) : FillsAt G A 0 (vertex G g - vertex G 1) :=
  ((Subgroup.closure_le (pathSubgroup G A)).mpr (fun a ha =>
    mem_pathSubgroup_of_mem G hA.one_mem ha (hA.inv_mem a ha))) hg

structure ControlledNullBelow (f : G →* G) (A : Set G) (n : ℕ) where
  bound : Set G
  isBound : IsBound G bound
  homotopy : Chain G →ₗ[ℤ] Chain G
  degree : ∀ m c, c ∈ degreeModule G m → homotopy c ∈ degreeModule G (m+1)
  controlled : ∀ c, c ∈ controlledModule G A → homotopy c ∈ controlledModule G bound
  zero : ∀ m, n ≤ m → ∀ c, c ∈ degreeModule G m → homotopy c = 0
  equation : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
    boundary G (homotopy c) + homotopy (boundary G c) = mapChain G f c - K G 1 c

def inDegree (n : ℕ) (v : Simplex G → Chain G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s => if degree G s = n then v s else 0)

omit [Group G] in
@[simp] lemma inDegree_single (n : ℕ) (v : Simplex G → Chain G) (s : Simplex G) :
    inDegree G n v (Finsupp.single s 1) = if degree G s = n then v s else 0 := by
  simp [inDegree]

omit [Group G] in
lemma inDegree_eq_zero {n m : ℕ} (hnm : m ≠ n) (v : Simplex G → Chain G)
    {c : Chain G} (hc : c ∈ degreeModule G m) : inDegree G n v c = 0 := by
  apply BasedComplex.linear_eq_on_support (inDegree G n v) (0 : Chain G →ₗ[ℤ] Chain G) c
  intro s hs
  have hd : degree G s = m := hc hs
  simp only [inDegree_single,hd,ite_eq_right hnm,LinearMap.zero_apply]

omit [Group G] in
lemma inDegree_mem_degree {n : ℕ} (v : Simplex G → Chain G)
    (hv : ∀ s, degree G s = n → v s ∈ degreeModule G (n+1))
    {m : ℕ} {c : Chain G} (hc : c ∈ degreeModule G m) :
    inDegree G n v c ∈ degreeModule G (m+1) := by
  apply BasedComplex.map_mem_of_support (inDegree G n v) _ c
  intro s hs
  rw [inDegree_single]
  split_ifs with he
  · rw [← hc hs,he]
    exact hv s he
  · exact Submodule.zero_mem _

lemma inDegree_mem_controlled {n : ℕ} (v : Simplex G → Chain G) {A B : Set G}
    (hv : ∀ s, degree G s = n → hasPropagation G A s → v s ∈ controlledModule G B)
    {c : Chain G} (hc : c ∈ controlledModule G A) :
    inDegree G n v c ∈ controlledModule G B := by
  apply BasedComplex.map_mem_of_support (inDegree G n v) _ c
  intro s hs
  rw [inDegree_single]
  split_ifs with he
  · exact hv s he (hc hs)
  · exact Submodule.zero_mem _

theorem controlledNullBelow_one_of_paths (f : G →* G) (A B : Set G)
    (hB : IsBound G B) (hf : ∀ g, f g ∈ Subgroup.closure B) :
    Nonempty (ControlledNullBelow G f A 1) := by
  classical
  choose p hpd hpb hp using fun g => path_of_mem_closure G hB (hf g)
  let v : Simplex G → Chain G := fun s => p s.1
  let J := inDegree G 0 v
  refine ⟨⟨B,hB,J,?_,?_,?_,?_⟩⟩
  · intro m c hc
    exact inDegree_mem_degree G v (fun s _ => hpd s.1) hc
  · intro c hc
    exact inDegree_mem_controlled G v (fun s _ _ => hpb s.1) hc
  · intro m hm c hc
    exact inDegree_eq_zero G (by omega) v hc
  · intro m hm c hc _
    have hm0 : m = 0 := by omega
    subst m
    rw [boundary_eq_zero_of_degree_zero G hc,map_zero,add_zero]
    apply BasedComplex.linear_eq_on_support (boundary G ∘ₗ J) (mapChain G f - K G 1) c
    intro s hs
    have hdeg : degree G s = 0 := hc hs
    have ht : s.2 = [] := List.length_eq_zero_iff.mp hdeg
    have he : Finsupp.single s 1 = vertex G s.1 := by cases s; simp_all [vertex,simplexVertex]
    change boundary G (J (Finsupp.single s 1)) = _
    rw [inDegree_single,ite_eq_left hdeg]
    change boundary G (p s.1) = mapChain G f (Finsupp.single s 1) - K G 1 (Finsupp.single s 1)
    rw [hp,he,mapChain_vertex,K_apply,augmentation_vertex,one_smul]

theorem controlledNullBelow_one_of_factorization {P : Type*} [Group P] [Group.FG P]
    (a : G →* P) (b : P →* G) (A : Set G) :
    Nonempty (ControlledNullBelow G (b.comp a) A 1) := by
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG P)
  let B := symmetricClosure G (b '' S)
  apply controlledNullBelow_one_of_paths G (b.comp a) A B
    (isBound_symmetricClosure G (hfin.image b))
  intro g
  apply Subgroup.closure_mono (subset_symmetricClosure G (b '' S))
  rw [← MonoidHom.map_closure,hS]
  exact Subgroup.mem_map.mpr ⟨a g,Subgroup.mem_top _,rfl⟩

end

variable (G : Type*) [Group G]

@[simp] lemma mapChain_K_one (g : G →* G) (c : Chain G) :
    mapChain G g (K G 1 c) = K G 1 c := by
  rw [mapChain_K]
  simp only [map_one,K_apply,augmentation_mapChain]

omit [Group G] in
lemma K_eq_zero_of_degree {n : ℕ} (hn : n ≠ 0) (a : G) {c : Chain G}
    (hc : c ∈ degreeModule G n) : K G a c = 0 := by
  rw [K_apply,augmentation_eq_zero_of_degree G hn hc,zero_smul]

def ControlledNullBelow.postcompose {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) (g : G →* G) :
    ControlledNullBelow G (g.comp f) A n where
  bound := g '' H.bound
  isBound := H.isBound.image G g
  homotopy := mapChain G g ∘ₗ H.homotopy
  degree m c hc := mapChain_mem_degree G g (H.degree m c hc)
  controlled c hc := mapChain_mem_controlled G G g (H.controlled c hc)
  zero m hm c hc := by simp only [LinearMap.comp_apply,H.zero m hm c hc,map_zero]
  equation m hm c hc ha := by
    have he := congrArg (mapChain G g) (H.equation m hm c hc ha)
    simpa only [map_add,map_sub,← boundary_mapChain,mapChain_comp,mapChain_K_one,
      MonoidHom.coe_comp,LinearMap.comp_apply] using he

omit [Group G] in

lemma inDegree_boundary_eq_zero {n m : ℕ} (hm : m ≤ n) (v : Simplex G → Chain G)
    {c : Chain G} (hc : c ∈ degreeModule G m) : inDegree G n v (boundary G c) = 0 := by
  cases m with
  | zero => rw [boundary_eq_zero_of_degree_zero G hc,map_zero]
  | succ m => exact inDegree_eq_zero G (by omega) v (boundary_mem_degreeModule G hc)

lemma ControlledNullBelow.obstruction_cycle {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) (hn : 0 < n) {c : Chain G}
    (hc : c ∈ degreeModule G n) (ha : c ∈ controlledModule G A) :
    boundary G (mapChain G f c - H.homotopy (boundary G c)) = 0 := by
  have hbd : boundary G c ∈ degreeModule G (n-1) := by
    apply boundary_mem_degreeModule G
    simpa only [Nat.sub_add_cancel hn] using hc
  have he := H.equation (n-1) (by omega) (boundary G c) hbd (boundary_mem_controlledModule G ha)
  simp only [boundary_boundary,map_zero,add_zero,K_boundary,sub_zero] at he
  rw [map_sub,boundary_mapChain,he,sub_self]

lemma ControlledNullBelow.obstruction_degree {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) (hn : 0 < n) {c : Chain G}
    (hc : c ∈ degreeModule G n) :
    mapChain G f c - H.homotopy (boundary G c) ∈ degreeModule G n := by
  have hn' : n-1+1 = n := Nat.sub_add_cancel hn
  have hbd : boundary G c ∈ degreeModule G (n-1) := by
    apply boundary_mem_degreeModule G
    rwa [hn']
  exact Submodule.sub_mem _ (mapChain_mem_degree G f hc) (by simpa only [hn'] using H.degree _ _ hbd)

lemma ControlledNullBelow.obstruction_controlled {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) {c : Chain G} (ha : c ∈ controlledModule G A) :
    mapChain G f c - H.homotopy (boundary G c) ∈ controlledModule G (f '' A ∪ H.bound) := by
  exact Submodule.sub_mem _
    (controlledModule_mono G Set.subset_union_left (mapChain_mem_controlled G G f ha))
    (controlledModule_mono G Set.subset_union_right (H.controlled _ (boundary_mem_controlledModule G ha)))

theorem ControlledNullBelow.extend {f : G →* G} {A : Set G} {n : ℕ}
    (H : ControlledNullBelow G f A n) (hn : 0 < n)
    (g : G →* G) {B : Set G} (hB : IsBound G B)
    (hfill : ∀ c, c ∈ degreeModule G n → c ∈ controlledModule G (f '' A ∪ H.bound) →
      boundary G c = 0 → FillsAt G B n (mapChain G g c)) :
    Nonempty (ControlledNullBelow G (g.comp f) A (n+1)) := by
  classical
  let S := {s : Simplex G // ListChains.degree G s = n ∧ hasPropagation G A s}
  let r (s : Simplex G) := mapChain G f (Finsupp.single s 1) - H.homotopy (boundary G (Finsupp.single s 1))
  have hr (s : S) : FillsAt G B n (mapChain G g (r s)) := by
    have hd : Finsupp.single s.val 1 ∈ degreeModule G n := FreeTensor.single_mem_supported {s : Simplex G | ListChains.degree G s = n} s.property.1 1
    have ha : Finsupp.single s.val 1 ∈ controlledModule G A := FreeTensor.single_mem_supported _ s.property.2 1
    exact hfill _ (H.obstruction_degree G hn hd) (H.obstruction_controlled G ha) (H.obstruction_cycle G hn hd ha)
  choose v hvd hva hvb using hr
  let v' (s : Simplex G) : Chain G := if h : ListChains.degree G s = n ∧ hasPropagation G A s then v ⟨s,h⟩ else 0
  let L := inDegree G n v'
  let Q := H.postcompose G g
  have hv'd (s : Simplex G) (_hs : ListChains.degree G s = n) : v' s ∈ degreeModule G (n+1) := by
    dsimp only [v']
    split_ifs with h
    · exact hvd ⟨s,h⟩
    · exact Submodule.zero_mem _
  have hv'a (s : Simplex G) (hd : ListChains.degree G s = n) (ha : hasPropagation G A s) :
      v' s ∈ controlledModule G B := by
    dsimp only [v']
    rw [dite_eq_left ⟨hd,ha⟩]
    exact hva ⟨s,hd,ha⟩
  have hLd (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      L c ∈ degreeModule G (m+1) := inDegree_mem_degree G v' hv'd hc
  have hLa (c : Chain G) (hc : c ∈ controlledModule G A) :
      L c ∈ controlledModule G B := inDegree_mem_controlled G v' hv'a hc
  refine ⟨⟨Q.bound ∪ B,Q.isBound.union G hB,Q.homotopy + L,?_,?_,?_,?_⟩⟩
  · intro m c hc
    exact Submodule.add_mem _ (Q.degree m c hc) (hLd m c hc)
  · intro c hc
    exact Submodule.add_mem _
      (controlledModule_mono G Set.subset_union_left (Q.controlled c hc))
      (controlledModule_mono G Set.subset_union_right (hLa c hc))
  · intro m hm c hc
    simp only [LinearMap.add_apply,Q.zero m (by omega) c hc]
    rw [inDegree_eq_zero G (by omega) v' hc,add_zero]
  · intro m hm c hc ha
    by_cases hmn : m < n
    · have hLc : L c = 0 := inDegree_eq_zero G (by omega) v' hc
      have hLdc : L (boundary G c) = 0 := inDegree_boundary_eq_zero G (by omega) v' hc
      simpa only [LinearMap.add_apply,hLc,hLdc,add_zero] using Q.equation m hmn c hc ha
    · have heqn : m = n := by omega
      subst m
      apply BasedComplex.linear_eq_on_support
        (boundary G ∘ₗ (Q.homotopy + L) + (Q.homotopy + L) ∘ₗ boundary G)
        (mapChain G (g.comp f) - K G 1) c
      intro s hs
      have hd : ListChains.degree G s = n := hc hs
      have hpa : hasPropagation G A s := ha hs
      have hsd : Finsupp.single s 1 ∈ degreeModule G n := FreeTensor.single_mem_supported {s : Simplex G | ListChains.degree G s = n} hd 1
      have hQ := Q.zero n le_rfl (Finsupp.single s 1) hsd
      have hL : L (boundary G (Finsupp.single s 1)) = 0 := inDegree_boundary_eq_zero G le_rfl v' hsd
      have hK := K_eq_zero_of_degree G (by omega : n ≠ 0) 1 hsd
      have hLv : L (Finsupp.single s 1) = v ⟨s,hd,hpa⟩ := by
        simp only [L,inDegree_single,ite_eq_left hd]
        exact dite_eq_left (show ListChains.degree G s = n ∧ hasPropagation G A s from ⟨hd,hpa⟩)
      simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,hQ,zero_add,hL,add_zero,hK,sub_zero,hLv]
      rw [hvb]
      change mapChain G g (mapChain G f (Finsupp.single s 1) - H.homotopy (boundary G (Finsupp.single s 1))) +
        mapChain G g (H.homotopy (boundary G (Finsupp.single s 1))) = _
      rw [map_sub,sub_add_cancel,mapChain_comp]
      rfl

end ListChains

end

end OAI
