import Mathlib
import OAI.GroupTheory.FiniteType.FiniteIdempotentDiagrams
import OAI.GroupTheory.FiniteType.ListChainsMapChainComp

namespace OAI

noncomputable section
namespace BinaryPrefixOperators
section

variable (K : Type*) [CommRing K]

abbrev Space := Stream' (Fin 2) →₀ K

noncomputable def left (i : Fin 2) : Module.End K (Space K) :=
  Finsupp.lmapDomain K K (Stream'.cons i)

noncomputable def right (i : Fin 2) : Module.End K (Space K) :=
  Finsupp.linearCombination K fun x : Stream' (Fin 2) =>
    if x.head = i then Finsupp.single x.tail 1 else 0

@[simp] lemma left_single (i : Fin 2) (x : Stream' (Fin 2)) (a : K) :
    left K i (Finsupp.single x a) = Finsupp.single (Stream'.cons i x) a := by
  simp [left]

@[simp] lemma right_single (i : Fin 2) (x : Stream' (Fin 2)) (a : K) :
    right K i (Finsupp.single x a) =
      if x.head = i then Finsupp.single x.tail a else 0 := by
  by_cases h : x.head = i <;> simp [right, h]

lemma right_left (i j : Fin 2) :
    right K i * left K j = if i = j then 1 else 0 := by
  apply Finsupp.lhom_ext
  intro x a
  by_cases h : i = j
  · subst j
    simp [Module.End.mul_apply]
  · simp [Module.End.mul_apply, h, Ne.symm h]

lemma partition : left K 0 * right K 0 + left K 1 * right K 1 = 1 := by
  apply Finsupp.lhom_ext
  intro x a
  have hx := Stream'.cons_head_tail x
  have hx0 : x.head = 0 ∨ x.head = 1 := by omega
  rcases hx0 with h | h
  · simpa [Module.End.mul_apply, h] using congrArg (fun y => Finsupp.single y a) hx
  · simpa [Module.End.mul_apply, h] using congrArg (fun y => Finsupp.single y a) hx

noncomputable def algebra : Subalgebra K (Module.End K (Space K)) :=
  Algebra.adjoin K (Set.range (left K) ∪ Set.range (right K))

noncomputable instance algebraRing : Ring (algebra K) :=
  Subalgebra.toRing (R := K) (A := Module.End K (Space K)) (algebra K)

noncomputable def l (i : Fin 2) : algebra K :=
  ⟨left K i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩

noncomputable def r (i : Fin 2) : algebra K :=
  ⟨right K i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩

lemma r_l (i j : Fin 2) : r K i * l K j = if i = j then 1 else 0 := by
  apply Subtype.ext
  by_cases h : i = j <;> simp [r, l, h, right_left]

lemma l_r_partition : l K 0 * r K 0 + l K 1 * r K 1 = 1 := by
  apply Subtype.ext
  exact partition K

end

open FiniteIdempotentDiagrams

variable (K : Type*) [CommRing K]

@[simp] lemma r_l_mul (i j : Fin 2) (x : algebra K) :
    r K i * (l K j * x) = if i = j then x else 0 := by
  rw [← mul_assoc, r_l]
  split <;> simp

noncomputable def sources (i j : Fin 3) : algebra K :=
  (![![(l K 0 * l K 0), (l K 0 * l K 1), l K 1],
      ![(l K 0 * l K 0 * l K 0), (l K 0 * l K 1), l K 1],
      ![(l K 0 * l K 0 * l K 1), (l K 0 * l K 1), l K 1]] :
    Fin 3 → Fin 3 → algebra K) i j

noncomputable def targets (i j : Fin 3) : algebra K :=
  (![![(r K 0 * r K 0), (r K 1 * r K 0), r K 1],
      ![(r K 0 * r K 0 * r K 0), (r K 1 * r K 0), r K 1],
      ![(r K 1 * r K 0 * r K 0), (r K 1 * r K 0), r K 1]] :
    Fin 3 → Fin 3 → algebra K) i j

lemma targets_sources (i j k : Fin 3) :
    targets K i j * sources K i k = if j = k then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [targets, sources, mul_assoc, r_l_mul, r_l]

noncomputable def copy (i : Fin 3) : Mat3 K →ₙ+* algebra K :=
  matrixCopy (sources K i) (targets K i) (targets_sources K i)

@[simp] lemma copy_diagonal (i j : Fin 3) :
    copy K i (diagonalUnit j) = sources K i j * targets K i j :=
  matrixCopy_diagonal _ _ _ _

lemma first_one : copy K 0 1 = 1 := by
  rw [← three_diagonal_sum, map_add, map_add, copy_diagonal, copy_diagonal, copy_diagonal]
  simp only [sources, targets, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  calc l K 0 * l K 0 * (r K 0 * r K 0) + l K 0 * l K 1 * (r K 1 * r K 0) +
      l K 1 * r K 1 = l K 0 * (l K 0 * r K 0 + l K 1 * r K 1) * r K 0 +
      l K 1 * r K 1 := by noncomm_ring
    _ = 1 := by rw [l_r_partition]; simpa using l_r_partition K

lemma first_partition : sources K 0 0 * targets K 0 0 =
    sources K 1 0 * targets K 1 0 + sources K 2 0 * targets K 2 0 := by
  simp only [sources, targets, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  calc l K 0 * l K 0 * (r K 0 * r K 0) =
      l K 0 * l K 0 * (l K 0 * r K 0 + l K 1 * r K 1) * (r K 0 * r K 0) := by
        rw [l_r_partition, mul_one]
    _ = _ := by noncomm_ring

noncomputable def threeCopies : ThreeCopies K (algebra K) where
  copy := copy K
  first_one := first_one K
  common_second i := by fin_cases i <;> simp [sources, targets]
  common_third i := by fin_cases i <;> simp [sources, targets]
  partition := by simpa only [copy_diagonal] using first_partition K
  partition_orthogonal := by simp [sources, targets, mul_assoc, r_l_mul]
  partition_orthogonal' := by simp [sources, targets, mul_assoc, r_l_mul]

noncomputable def idempotents : Set (algebra K) :=
  {E | E = 1 ∨ E * E = E ∧ ∃ (i : Fin 3) (M : Mat3 K), copy K i M = E}

lemma identity_mem : (1 : algebra K) ∈ idempotents K := Or.inl rfl

lemma idempotents_are_idempotent {E : algebra K} (hE : E ∈ idempotents K) :
    E * E = E := by
  rcases hE with rfl | hE
  · exact one_mul _
  · exact hE.1

lemma idempotents_finite [Finite K] : (idempotents K).Finite := by
  apply ((Set.finite_range fun x : Fin 3 × Mat3 K => copy K x.1 x.2).insert 1).subset
  rintro x (rfl | ⟨_, i, M, rfl⟩)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨(i, M), rfl⟩

lemma system_subset : (threeCopies K).system ⊆ idempotents K := by
  rintro E (rfl | ⟨i, M, hM, rfl⟩)
  · exact identity_mem K
  · exact Or.inr ⟨by rw [← map_mul, hM], i, M, rfl⟩

theorem finite_idempotents (p : ℕ) [CharP K p] {T : Type*} [AddCommGroup T]
    (z : algebra K → T) (hz : OrthogonalAdditiveOn (idempotents K) z) : p • z 1 = 0 := by
  apply (threeCopies K).annihilates_one p z
  intro E P hE hP hSum hEP hPE
  exact hz E P (system_subset K hE) (system_subset K hP) (system_subset K hSum) hEP hPE

def AssignmentAdditive {T : Type*} [AddCommGroup T] (z : idempotents K → T) : Prop :=
  ∀ E P : idempotents K, ∀ hSum : E.val + P.val ∈ idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 →
    z ⟨E.val + P.val, hSum⟩ = z E + z P

theorem finite_idempotent_assignment (p : ℕ) [CharP K p]
    {T : Type*} [AddCommGroup T] (z : idempotents K → T) (hz : AssignmentAdditive K z) :
    p • z ⟨1, identity_mem K⟩ = 0 := by
  classical
  let z' : algebra K → T := fun E => if h : E ∈ idempotents K then z ⟨E, h⟩ else 0
  have hz' : OrthogonalAdditiveOn (idempotents K) z' := by
    intro E P hE hP hSum hEP hPE
    simp only [z', dite_eq_left hE, dite_eq_left hP, dite_eq_left hSum]
    exact hz ⟨E, hE⟩ ⟨P, hP⟩ hSum hEP hPE
  simpa only [z', dite_eq_left (identity_mem K)] using finite_idempotents K p z' hz'

end BinaryPrefixOperators

namespace ListChains
section

variable (G : Type*) [Group G]

def boundedBoundaries (B : Set G) (n : ℕ) : Submodule ℤ (Chain G) :=
  (degreeModule G (n+1) ⊓ controlledModule G B).map (boundary G)

lemma fillsAt_iff_mem_boundaries {B : Set G} {n : ℕ} {z : Chain G} :
    FillsAt G B n z ↔ z ∈ boundedBoundaries G B n := by
  simp only [FillsAt,boundedBoundaries,Submodule.mem_map,Submodule.mem_inf]
  constructor
  · rintro ⟨w,hd,ha,he⟩
    exact ⟨w,⟨hd,ha⟩,he⟩
  · rintro ⟨w,⟨hd,ha⟩,he⟩
    exact ⟨w,hd,ha,he⟩

lemma fillsAt_iff_quotient_zero {B : Set G} {n : ℕ} {z : Chain G} :
    FillsAt G B n z ↔ (boundedBoundaries G B n).mkQ z = 0 := by
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,fillsAt_iff_mem_boundaries]

structure IdempotentSplittings (K : Type*) [CommRing K] (f : G →* G) where
  map : BinaryPrefixOperators.idempotents K → (G →* G)
  identity : map ⟨1,BinaryPrefixOperators.identity_mem K⟩ = f
  commute : ∀ E P : BinaryPrefixOperators.idempotents K,
    ∀ _hSum : E.val + P.val ∈ BinaryPrefixOperators.idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 → ∀ u v, Commute (map E u) (map P v)
  addition : ∀ E P : BinaryPrefixOperators.idempotents K,
    ∀ hSum : E.val + P.val ∈ BinaryPrefixOperators.idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 →
    ∀ u, map ⟨E.val+P.val,hSum⟩ u = map E u * map P u

theorem IdempotentSplittings.uniform_nsmul_fillings
    {K : Type*} [CommRing K] [Finite K] (p : ℕ) [CharP K p]
    {f g : G →* G} (F : IdempotentSplittings G K f)
    {A : Set G} (hA : IsBound G A) {n : ℕ} (hn : 0 < n)
    (H : ControlledNullBelow G g A n) :
    ∃ B : Set G, IsBound G B ∧ ∀ z, z ∈ degreeModule G n →
      z ∈ controlledModule G A → boundary G z = 0 →
      FillsAt G B n (p • mapChain G (f ∘ g) z) := by
  classical
  let I := BinaryPrefixOperators.idempotents K
  let : Fintype I := (BinaryPrefixOperators.idempotents_finite K).fintype
  let R := {r : I × I // r.1.val + r.2.val ∈ BinaryPrefixOperators.idempotents K ∧
    r.1.val*r.2.val = 0 ∧ r.2.val*r.1.val = 0}
  have hr (r : R) : ∃ B : Set G, IsBound G B ∧
      ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
      FillsAt G B n (mapChain G (fun x => F.map r.val.1 (g x) * F.map r.val.2 (g x)) z -
        mapChain G (F.map r.val.1 ∘ g) z - mapChain G (F.map r.val.2 ∘ g) z) := by
    exact controlled_commuting_additivity G g H.homotopy hn hA H.isBound
      H.degree (H.zero n le_rfl) H.controlled H.equation (F.map r.val.1) (F.map r.val.2)
      (F.commute r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2)
  choose B hB hfill using hr
  obtain ⟨C,hC,hBC⟩ := finite_common_bound G B hB
  refine ⟨C,hC,?_⟩
  intro z hzd hza hz
  let π := (boundedBoundaries G C n).mkQ
  let Z : I → Chain G ⧸ boundedBoundaries G C n := fun E => π (mapChain G (F.map E ∘ g) z)
  have hZ : BinaryPrefixOperators.AssignmentAdditive K Z := by
    intro E P hSum hEP hPE
    let r : R := ⟨(E,P),hSum,hEP,hPE⟩
    have hw := (hfill r z hzd hza hz).mono G (hBC r)
    have hfun : (fun x => F.map E (g x)*F.map P (g x)) =
        (F.map ⟨E.val+P.val,hSum⟩ ∘ g) := funext fun x => (F.addition E P hSum hEP hPE (g x)).symm
    change FillsAt G C n (mapChain G (fun x => F.map E (g x)*F.map P (g x)) z -
      mapChain G (F.map E ∘ g) z - mapChain G (F.map P ∘ g) z) at hw
    rw [hfun] at hw
    have he := (fillsAt_iff_quotient_zero G).mp hw
    change Z ⟨E.val+P.val,hSum⟩ = Z E + Z P
    apply sub_eq_zero.mp
    simpa only [map_sub,sub_add_eq_sub_sub] using he
  have hkill := BinaryPrefixOperators.finite_idempotent_assignment K p Z hZ
  apply (fillsAt_iff_quotient_zero G).mpr
  rw [map_nsmul]
  simpa only [Z,F.identity] using hkill

theorem uniform_fillings_from_partial_homotopy
    {f g : G →* G} (F₂ : IdempotentSplittings G (ZMod 2) f)
    (F₃ : IdempotentSplittings G (ZMod 3) f)
    {A : Set G} (hA : IsBound G A) {n : ℕ} (hn : 0 < n)
    (H : ControlledNullBelow G g A n) :
    ∃ B : Set G, IsBound G B ∧ ∀ z, z ∈ degreeModule G n →
      z ∈ controlledModule G A → boundary G z = 0 →
      FillsAt G B n (mapChain G (f ∘ g) z) := by
  obtain ⟨B₂,hB₂,h₂⟩ := F₂.uniform_nsmul_fillings G 2 hA hn H
  obtain ⟨B₃,hB₃,h₃⟩ := F₃.uniform_nsmul_fillings G 3 hA hn H
  refine ⟨B₂ ∪ B₃,hB₂.union G hB₃,?_⟩
  intro z hzd hza hz
  have h := ((h₃ z hzd hza hz).mono G Set.subset_union_right).add G
    (((h₂ z hzd hza hz).mono G Set.subset_union_left).neg G)
  have he : 3 • mapChain G (f ∘ g) z + -(2 • mapChain G (f ∘ g) z) = mapChain G (f ∘ g) z := by
    simp only [succ_nsmul,zero_nsmul,zero_add]
    abel
  rwa [he] at h

def iterateHom (f : G →* G) : ℕ → G →* G
  | 0 => MonoidHom.id G
  | k+1 => f.comp (iterateHom f k)
@[simp] lemma iterateHom_zero (f : G →* G) : iterateHom G f 0 = MonoidHom.id G := rfl
@[simp] lemma iterateHom_one (f : G →* G) : iterateHom G f 1 = f := by ext; rfl
lemma iterateHom_add (f : G →* G) (k l : ℕ) :
    iterateHom G f (k+l) = (iterateHom G f k).comp (iterateHom G f l) := by
  induction k with
  | zero => simp only [Nat.zero_add, iterateHom_zero, MonoidHom.id_comp]
  | succ k ih =>
    rw [Nat.succ_add,iterateHom,ih,iterateHom]
    rfl

def UniformFillings (f : G →* G) (n : ℕ) : Prop :=
  ∀ A : Set G, IsBound G A → ∃ k : ℕ, ∃ B : Set G, IsBound G B ∧
    ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
      (n = 0 → augmentation G z = 0) → FillsAt G B n (mapChain G (iterateHom G f k) z)

theorem partial_homotopy_from_uniform (f : G →* G)
    (hbase : ∀ A, Nonempty (ControlledNullBelow G f A 1))
    (n : ℕ) (hn : 0 < n)
    (hfill : ∀ q, 0 < q → q < n → UniformFillings G f q)
    (A : Set G) (hA : IsBound G A) :
    ∃ k, Nonempty (ControlledNullBelow G (iterateHom G f k) A n) := by
  induction n with
  | zero => omega
  | succ q ih =>
    by_cases hq : q = 0
    · subst q
      exact ⟨1,by simpa only [iterateHom_one] using hbase A⟩
    · have hq' : 0 < q := by omega
      obtain ⟨k,⟨H⟩⟩ := ih hq' (fun j hj hjq => hfill j hj (by omega))
      obtain ⟨l,B,hB,hBl⟩ := hfill q hq' (by omega)
        ((iterateHom G f k) '' A ∪ H.bound)
        ((hA.image G (iterateHom G f k)).union G H.isBound)
      have hext := H.extend G hq' (iterateHom G f l) hB
        (fun c hcd hca hcz => hBl c hcd hca hcz (fun hq0 => (hq hq0).elim))
      exact ⟨l+k,by simpa only [iterateHom_add] using hext⟩

theorem uniform_fillings_of_factorization_and_splittings
    {P : Type*} [Group P] [Group.FG P] (a : G →* P) (b : P →* G)
    (F₂ : IdempotentSplittings G (ZMod 2) (b.comp a))
    (F₃ : IdempotentSplittings G (ZMod 3) (b.comp a)) :
    ∀ n, UniformFillings G (b.comp a) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hA
    by_cases hn : n = 0
    · subst n
      obtain ⟨H⟩ := controlledNullBelow_one_of_factorization G a b A
      refine ⟨1,H.bound,H.isBound,?_⟩
      intro z hzd hza hz hred
      refine ⟨H.homotopy z,H.degree 0 z hzd,H.controlled z hza,?_⟩
      have he := H.equation 0 (by decide) z hzd hza
      simpa only [hz,map_zero,add_zero,K_apply,hred rfl,zero_smul,sub_zero,iterateHom_one] using he
    · have hn' : 0 < n := by omega
      obtain ⟨k,⟨H⟩⟩ := partial_homotopy_from_uniform G (b.comp a)
        (controlledNullBelow_one_of_factorization G a b) n hn'
        (fun q _ hq => ih q hq) A hA
      obtain ⟨B,hB,hfill⟩ := uniform_fillings_from_partial_homotopy G F₂ F₃ hA hn' H
      refine ⟨1+k,B,hB,?_⟩
      intro z hzd hza hz _
      simpa only [iterateHom_add,iterateHom_one,MonoidHom.coe_comp] using hfill z hzd hza hz

theorem UniformFillings.families {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f n) (hn : 0 < n)
    {I C : Type*} (z : I → C →₀ Chain G)
    (hdegree : ∀ i c, z i c ∈ degreeModule G n)
    (hcycle : ∀ i c, boundary G (z i c) = 0)
    {A : Set G} (hA : IsBound G A)
    (hcontrol : ∀ i c, z i c ∈ controlledModule G A) :
    ∃ k : ℕ, ∃ B : Set G, IsBound G B ∧ ∃ w : I → C →₀ Chain G,
      ∀ i c, w i c ∈ degreeModule G (n+1) ∧
        w i c ∈ controlledModule G B ∧
        boundary G (w i c) = mapChain G (iterateHom G f k) (z i c) := by
  classical
  obtain ⟨k,B,hB,hfill⟩ := hf A hA
  have hw (i : I) (c : C) := hfill (z i c) (hdegree i c) (hcontrol i c)
    (hcycle i c) (by omega)
  choose v hvd hva hvb using hw
  let w (i : I) : C →₀ Chain G := Finsupp.onFinset (z i).support
    (fun c => if c ∈ (z i).support then v i c else 0)
    (by intro c hc; by_contra h; simp only [ite_eq_right h] at hc; exact hc rfl)
  refine ⟨k,B,hB,w,?_⟩
  intro i c
  by_cases hc : c ∈ (z i).support
  · simp only [w,Finsupp.onFinset_apply,ite_eq_left hc]
    exact ⟨hvd i c,hva i c,hvb i c⟩
  · have hz : z i c = 0 := Finsupp.notMem_support_iff.mp hc
    simp only [w,Finsupp.onFinset_apply,ite_eq_right hc,hz,map_zero]
    exact ⟨Submodule.zero_mem _,Submodule.zero_mem _,trivial⟩

theorem UniformFillings.translated_families {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f n) (hn : 0 < n)
    {I C : Type*} (z : I → C →₀ Chain G)
    (hdegree : ∀ i c, z i c ∈ degreeModule G n)
    (hcycle : ∀ i c, boundary G (z i c) = 0)
    {A : Set G} (hA : IsBound G A)
    (hcontrol : ∀ i c, z i c ∈ controlledModule G A)
    (origin : ℕ → I → C → G) :
    ∃ k : ℕ, ∃ B : Set G, IsBound G B ∧ ∃ w : I → C →₀ Chain G,
      ∀ i c, w i c ∈ degreeModule G (n+1) ∧
        w i c ∈ controlledModule G B ∧
        boundary G (w i c) =
          mapChain G (fun x => origin k i c * iterateHom G f k x) (z i c) := by
  classical
  obtain ⟨k,B,hB,w,hw⟩ := hf.families G hn z hdegree hcycle hA hcontrol
  let v (i : I) : C →₀ Chain G := Finsupp.onFinset (w i).support
    (fun c => mapChain G (fun x => origin k i c*x) (w i c))
    (by intro c hc; by_contra h; apply hc
        rw [Finsupp.notMem_support_iff.mp h,map_zero])
  refine ⟨k,B,hB,v,?_⟩
  intro i c
  dsimp only [v,Finsupp.onFinset_apply]
  refine ⟨mapChain_mem_degree G _ (hw i c).1,
    leftTranslate_mem_controlled G _ (hw i c).2.1,?_⟩
  rw [boundary_mapChain,(hw i c).2.2,mapChain_comp]
  rfl

end

variable (G : Type*) {H K C D E : Type*}

def cosetModule (P : Submodule ℤ (Chain G)) : Submodule ℤ (C →₀ Chain G) where
  carrier := {z | ∀ c, z c ∈ P}
  zero_mem' := fun _ => P.zero_mem
  add_mem' := fun hz hw c => P.add_mem (hz c) (hw c)
  smul_mem' := fun r _ hz c => P.smul_mem r (hz c)

lemma single_mem_cosetModule (P : Submodule ℤ (Chain G)) (c : C) {z : Chain G}
    (hz : z ∈ P) : Finsupp.single c z ∈ cosetModule G P := by
  classical
  intro d
  by_cases h : c = d
  · subst d; simpa only [Finsupp.single_eq_same] using hz
  · simpa only [Finsupp.single_eq_of_ne (Ne.symm h)] using P.zero_mem

def cosetMap (σ : C → D) (ψ : C → G → H) :
    (C →₀ Chain G) →ₗ[ℤ] (D →₀ Chain H) :=
  Finsupp.lsum ℤ (fun c => (Finsupp.lsingle (σ c)).comp (mapChain G (ψ c)))

@[simp] lemma cosetMap_single (σ : C → D) (ψ : C → G → H) (c : C) (z : Chain G) :
    cosetMap G σ ψ (Finsupp.single c z) = Finsupp.single (σ c) (mapChain G (ψ c) z) := by
  simp [cosetMap]

lemma cosetMap_mem (σ : C → D) (ψ : C → G → H)
    (P : Submodule ℤ (Chain G)) (Q : Submodule ℤ (Chain H))
    (hψ : ∀ c z, z ∈ P → mapChain G (ψ c) z ∈ Q)
    {z : C →₀ Chain G} (hz : z ∈ cosetModule G P) :
    cosetMap G σ ψ z ∈ cosetModule H Q := by
  classical
  change (Finsupp.lsum ℤ _) z ∈ _
  rw [Finsupp.lsum_apply]
  apply Submodule.sum_mem
  intro c _
  exact single_mem_cosetModule H Q (σ c) (hψ c (z c) (hz c))

lemma cosetMap_comp (σ : C → D) (τ : D → E) (ψ : C → G → H) (χ : D → H → K)
    (z : C →₀ Chain G) :
    cosetMap H τ χ (cosetMap G σ ψ z) =
      cosetMap G (τ ∘ σ) (fun c => χ (σ c) ∘ ψ c) z := by
  have h : (cosetMap H τ χ).comp (cosetMap G σ ψ) =
      cosetMap G (τ ∘ σ) (fun c => χ (σ c) ∘ ψ c) := by
    apply Finsupp.lhom_ext
    intro c z
    simp only [LinearMap.comp_apply,cosetMap_single,mapChain_comp,Function.comp_apply]
  exact LinearMap.congr_fun h z

@[simp] lemma cosetMap_id (z : C →₀ Chain G) : cosetMap G id (fun _ => id) z = z := by
  have h : cosetMap G (id : C → C) (fun _ => id) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro c z
    simp only [cosetMap_single,mapChain_id,id_eq,LinearMap.id_apply]
  exact LinearMap.congr_fun h z

def cosetBoundary : (C →₀ Chain G) →ₗ[ℤ] (C →₀ Chain G) :=
  Finsupp.mapRange.linearMap (boundary G)

@[simp] lemma cosetBoundary_apply (z : C →₀ Chain G) (c : C) :
    cosetBoundary G z c = boundary G (z c) := rfl

@[simp] lemma cosetBoundary_single (c : C) (z : Chain G) :
    cosetBoundary G (Finsupp.single c z) = Finsupp.single c (boundary G z) := by
  change Finsupp.mapRange (boundary G) (map_zero _) _ = _
  exact Finsupp.mapRange_single

@[simp] lemma cosetBoundary_squared (z : C →₀ Chain G) :
    cosetBoundary G (cosetBoundary G z) = 0 := by ext c s; simp

lemma cosetBoundary_cosetMap (σ : C → D) (ψ : C → G → H) (z : C →₀ Chain G) :
    cosetBoundary H (cosetMap G σ ψ z) = cosetMap G σ ψ (cosetBoundary G z) := by
  have h : (cosetBoundary H).comp (cosetMap G σ ψ) =
      (cosetMap G σ ψ).comp (cosetBoundary G) := by
    apply Finsupp.lhom_ext
    intro c z
    simp only [LinearMap.comp_apply,cosetMap_single,cosetBoundary_single,boundary_mapChain]
  exact LinearMap.congr_fun h z

def mergeCosets (σ : C → D) : (C →₀ Chain G) →ₗ[ℤ] (D →₀ Chain G) :=
  Finsupp.lmapDomain (Chain G) ℤ σ

@[simp] lemma mergeCosets_single (σ : C → D) (c : C) (z : Chain G) :
    mergeCosets G σ (Finsupp.single c z) = Finsupp.single (σ c) z := by
  simp [mergeCosets]

lemma mergeCosets_eq (σ : C → D) :
    mergeCosets G σ = cosetMap G σ (fun _ => id) := by
  apply Finsupp.lhom_ext
  intro c z
  simp

lemma cosetBoundary_mergeCosets (σ : C → D) (z : C →₀ Chain G) :
    cosetBoundary G (mergeCosets G σ z) = mergeCosets G σ (cosetBoundary G z) := by
  rw [mergeCosets_eq,cosetBoundary_cosetMap]

end ListChains

end

end OAI
