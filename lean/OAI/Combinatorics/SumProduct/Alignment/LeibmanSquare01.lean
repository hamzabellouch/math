import Mathlib
import OAI.Geometry.NilpotentCharts.Coordinates
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement
namespace LeibmanSquare
open CubeFaces
variable {G : Type*} [Group G]

lemma level_normal (H : Filtration G) (h0 : H.level 0 = ⊤) (i : ℕ) :
    (H.level i).Normal where
  conj_mem x hx g := by
    have hg : g ∈ H.level 0 := by rw [h0]; trivial
    have hc := H.commutator_le 0 i (Subgroup.commutator_mem_commutator hg hx)
    simp only [zero_add] at hc
    have := (H.level i).mul_mem hc hx
    simpa [commutatorElement_def, mul_assoc] using this

 
def level (H : Filtration G) (h0 : H.level 0 = ⊤) (i : ℕ) : Subgroup (G × G) where
  carrier := {x | x.1 ∈ H.level i ∧ x.2 ∈ H.level i ∧ x.1⁻¹*x.2 ∈ H.level (i+1)}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha,hb,hab⟩ ⟨hc,hd,hcd⟩
    refine ⟨(H.level i).mul_mem ha hc, (H.level i).mul_mem hb hd, ?_⟩
    have hh := (level_normal H h0 (i+1)).conj_mem _ hab b.1⁻¹
    have hmul := (H.level (i+1)).mul_mem hh hcd
    simpa [mul_assoc] using hmul
  inv_mem' := by
    rintro a ⟨ha,hb,hab⟩
    refine ⟨(H.level i).inv_mem ha, (H.level i).inv_mem hb, ?_⟩
    have hh := (level_normal H h0 (i+1)).conj_mem _
      ((H.level (i+1)).inv_mem hab) a.1
    simpa [mul_assoc] using hh

lemma mem_level (H : Filtration G) (h0 : H.level 0 = ⊤) (i : ℕ) (x : G × G) :
    x ∈ level H h0 i ↔ x.1 ∈ H.level i ∧ x.2 ∈ H.level i ∧
      x.1⁻¹*x.2 ∈ H.level (i+1) := Iff.rfl

lemma level_antitone (H : Filtration G) (h0 : H.level 0 = ⊤) :
    Antitone (level H h0) := by
  intro i j hij x ⟨ha,hb,hab⟩
  exact ⟨H.antitone hij ha,H.antitone hij hb,H.antitone (by omega) hab⟩

lemma commutator_mem_level (H : Filtration G) (h0 : H.level 0 = ⊤)
    (i j : ℕ) {x y : G × G} (hx : x ∈ level H h0 i) (hy : y ∈ level H h0 j) :
    ⁅x,y⁆ ∈ level H h0 (i+j) := by
  rcases hx with ⟨hx1,hx2,hxd⟩
  rcases hy with ⟨hy1,hy2,hyd⟩
  refine ⟨H.commutator_le _ _ (Subgroup.commutator_mem_commutator hx1 hy1),
    H.commutator_le _ _ (Subgroup.commutator_mem_commutator hx2 hy2), ?_⟩
  let N := H.level (i+j+1)
  let : N.Normal := level_normal H h0 _
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have qx : q ⁅x.1⁻¹*x.2,y.2⁆ = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact H.antitone (by omega) (H.commutator_le _ _
      (Subgroup.commutator_mem_commutator hxd hy2))
  have qy : q ⁅x.1,y.1⁻¹*y.2⁆ = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact H.antitone (by omega) (H.commutator_le _ _
      (Subgroup.commutator_mem_commutator hx1 hyd))
  have he : q ⁅x.2,y.2⁆ = q ⁅x.1,y.1⁆ := by
    calc
      _ = q ⁅x.1*(x.1⁻¹*x.2),y.2⁆ := by simp
      _ = q ⁅x.1,y.2⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul]
        simp only [map_mul,map_inv,qx,mul_one,mul_inv_cancel,one_mul]
      _ = q ⁅x.1,y.1*(y.1⁻¹*y.2)⁆ := by simp
      _ = q ⁅x.1,y.1⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj]
        simp [map_mul,map_inv,qy,mul_assoc]
  change ⁅x.1,y.1⁆⁻¹*⁅x.2,y.2⁆ ∈ N
  apply (QuotientGroup.eq_one_iff _).mp
  change q (⁅x.1,y.1⁆⁻¹*⁅x.2,y.2⁆) = 1
  rw [map_mul,map_inv,he,inv_mul_cancel]

 
def filtration (H : Filtration G) (h0 : H.level 0 = ⊤) : Filtration (G × G) where
  level := level H h0
  antitone := level_antitone H h0
  commutator_le i j := Subgroup.commutator_le.mpr fun _ hx _ hy =>
    commutator_mem_level H h0 i j hx hy

lemma level_zero (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤) :
    level H h0 0 = ⊤ := by
  ext x
  simp [mem_level,h0,h1]

 
lemma last_level (H : Filtration G) (h0 : H.level 0 = ⊤) (s : ℕ)
    (hs : H.level (s+1) = ⊥) (x : G × G) :
    x ∈ level H h0 s ↔ x.1 ∈ H.level s ∧ x.1 = x.2 := by
  rw [mem_level,hs]
  simp only [Subgroup.mem_bot,inv_mul_eq_one]
  constructor
  · tauto
  · rintro ⟨hx,he⟩
    exact ⟨hx,he ▸ hx,he⟩

 
lemma last_central (H : Filtration G) (h0 : H.level 0 = ⊤) (s : ℕ)
    (hs : H.level (s+1) = ⊥) {x y : G × G}
    (hx : x ∈ level H h0 1) (hy : y ∈ level H h0 s) : Commute x y := by
  apply commutatorElement_eq_one_iff_commute.mp
  have hh := commutator_mem_level H h0 1 s hx hy
  have hbot : level H h0 (1+s) = ⊥ := by
    apply le_antisymm _ bot_le
    intro z ⟨hz1,hz2,_⟩
    have hz1' : z.1 = 1 := by simpa [Nat.add_comm,hs] using hz1
    have hz2' : z.2 = 1 := by simpa [Nat.add_comm,hs] using hz2
    exact Prod.ext hz1' hz2'
  simpa [hbot] using hh

 
def restricted (H : Filtration G) (h0 : H.level 0 = ⊤) :
    Filtration (level H h0 1) where
  level i := (level H h0 (max 1 i)).comap (level H h0 1).subtype
  antitone := by
    intro i j hij
    exact Subgroup.comap_mono (level_antitone H h0 (max_le_max_left 1 hij))
  commutator_le i j := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    change (↑⁅x,y⁆ : G × G) ∈ level H h0 (max 1 (i+j))
    have hc := commutator_mem_level H h0 (max 1 i) (max 1 j) hx hy
    exact level_antitone H h0 (by omega) hc

lemma restricted_zero (H : Filtration G) (h0 : H.level 0 = ⊤) :
    (restricted H h0).level 0 = ⊤ := by
  ext x
  simp only [restricted, max_eq_left (by omega : 0 ≤ 1), Subgroup.mem_comap,
    Subgroup.coe_subtype, Subgroup.mem_top, iff_true]
  exact x.property

lemma restricted_one (H : Filtration G) (h0 : H.level 0 = ⊤) :
    (restricted H h0).level 1 = ⊤ := by
  ext x
  simp only [restricted, max_self, Subgroup.mem_comap,
    Subgroup.coe_subtype, Subgroup.mem_top, iff_true]
  exact x.property

 

lemma last_normal (H : Filtration G) (h0 : H.level 0 = ⊤)
    {s : ℕ} (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥) :
    ((restricted H h0).level s).Normal where
  conj_mem x hx y := by
    change (↑(y*x*y⁻¹) : G × G) ∈ level H h0 (max 1 s)
    change (x : G × G) ∈ level H h0 (max 1 s) at hx
    rw [max_eq_right hs0] at hx ⊢
    have hc := last_central H h0 s hs y.property hx
    change (y : G × G) * x * (y : G × G)⁻¹ ∈ _
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hx

 
def mapFiltration {K : Type*} [Group K] (H : Filtration G) (φ : G →* K) :
    Filtration K where
  level i := (H.level i).map φ
  antitone := by
    intro i j hij
    exact Subgroup.map_mono (H.antitone hij)
  commutator_le i j := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (H.commutator_le i j)

 

theorem quotient_lowers_degree (H : Filtration G) (h0 : H.level 0 = ⊤)
    {s : ℕ} (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥) :
    let R := restricted H h0
    letI := last_normal H h0 hs0 hs
    let Q := mapFiltration R (QuotientGroup.mk' (R.level s))
    Q.level 0 = ⊤ ∧ Q.level 1 = ⊤ ∧ Q.level s = ⊥ := by
  let : ((restricted H h0).level s).Normal := last_normal H h0 hs0 hs
  dsimp only
  constructor
  · change ((restricted H h0).level 0).map _ = _
    rw [restricted_zero, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  constructor
  · change ((restricted H h0).level 1).map _ = _
    rw [restricted_one, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · change ((restricted H h0).level s).map _ = _
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

 

def pairConj (a b : G) : (G × G) ≃* (G × G) :=
  (MulAut.conj a).prodCongr (MulAut.conj b)

lemma conjugate_mod_next (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) (i : ℕ) {x : G} (hx : x ∈ H.level i) (a : G) :
    x⁻¹*(a*x*a⁻¹) ∈ H.level (i+1) := by
  have ha : a ∈ H.level 1 := by rw [h1]; trivial
  have hc := H.commutator_le 1 i (Subgroup.commutator_mem_commutator ha hx)
  have hc' : ⁅a,x⁆ ∈ H.level (i+1) := by simpa [Nat.add_comm] using hc
  have hh := (level_normal H h0 (i+1)).conj_mem _ hc' x⁻¹
  simpa [commutatorElement_def,mul_assoc] using hh

lemma pairConj_mem (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) (i : ℕ) (a b : G) {x : G × G}
    (hx : x ∈ level H h0 i) : pairConj a b x ∈ level H h0 i := by
  rcases hx with ⟨hx1,hx2,hxd⟩
  refine ⟨(level_normal H h0 i).conj_mem _ hx1 a,
    (level_normal H h0 i).conj_mem _ hx2 b,?_⟩
  have ha := conjugate_mod_next H h0 h1 i hx1 a
  have hb := conjugate_mod_next H h0 h1 i hx2 b
  have hh := (H.level (i+1)).mul_mem
    ((H.level (i+1)).mul_mem ((H.level (i+1)).inv_mem ha) hxd) hb
  change (a*x.1*a⁻¹)⁻¹*(b*x.2*b⁻¹) ∈ H.level (i+1)
  simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,
    mul_inv_cancel_left] using hh

lemma pairConj_last_fixed (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) (s : ℕ) (hs : H.level (s+1) = ⊥)
    (a b : G) {x : G × G} (hx : x ∈ level H h0 s) : pairConj a b x = x := by
  have ha := conjugate_mod_next H h0 h1 s hx.1 a
  have hb := conjugate_mod_next H h0 h1 s hx.2.1 b
  have he1 : a*x.1*a⁻¹ = x.1 := by
    symm
    simpa only [hs,Subgroup.mem_bot,inv_mul_eq_one] using ha
  have he2 : b*x.2*b⁻¹ = x.2 := by
    symm
    simpa only [hs,Subgroup.mem_bot,inv_mul_eq_one] using hb
  exact Prod.ext he1 he2

 

lemma pairConj_lattice (Γ : Subgroup G) {a b : G} (ha : a ∈ Γ) (hb : b ∈ Γ)
    {x : G × G} (hx : x ∈ Γ.prod Γ) : pairConj a b x ∈ Γ.prod Γ :=
  ⟨Γ.mul_mem (Γ.mul_mem ha hx.1) (Γ.inv_mem ha),
    Γ.mul_mem (Γ.mul_mem hb hx.2) (Γ.inv_mem hb)⟩

 

lemma orbit_normalization (Γ : Subgroup G) {a u γ : G}
    (ha : a = u*γ) (hγ : γ ∈ Γ) (x : G) :
    (QuotientGroup.mk (u * MulAut.conj γ (a⁻¹*x)) : G ⧸ Γ) =
      QuotientGroup.mk x := by
  subst a
  have he : u * MulAut.conj γ ((u*γ)⁻¹*x) = x*γ⁻¹ := by
    simp [MulAut.conj_apply,mul_assoc]
  rw [he]
  exact QuotientGroup.mk_mul_of_mem x (Γ.inv_mem hγ)

variable {A : Type*} [AddCommGroup A]

 
def diff (h : A) (f : A → G) (n : A) : G := (f n)⁻¹*f (n+h)

def iterDiff : List A → (A → G) → (A → G)
  | [], f => f
  | h::hs, f => iterDiff hs (diff h f)

 

def Polynomial (H : Filtration G) (k : ℕ) (f : A → G) : Prop :=
  ∀ hs n, iterDiff hs f n ∈ H.level (k+hs.length)

lemma iterDiff_append (hs ts : List A) (f : A → G) :
    iterDiff (hs++ts) f = iterDiff ts (iterDiff hs f) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih => exact ih _

lemma iterDiff_shift (hs : List A) (f : A → G) (t : A) :
    iterDiff hs (fun n => f (n+t)) = fun n => iterDiff hs f (n+t) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    change iterDiff hs (diff h (fun n => f (n+t))) = _
    have he : diff h (fun n => f (n+t)) = fun n => diff h f (n+t) := by
      funext n
      simp only [diff]
      congr 2; abel
    rw [he,ih]
    rfl

lemma iterDiff_hom {K : Type*} [Group K] (φ : G →* K) (hs : List A) (f : A → G) :
    iterDiff hs (fun n => φ (f n)) = fun n => φ (iterDiff hs f n) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    change iterDiff hs (diff h (fun n => φ (f n))) = _
    have he : diff h (fun n => φ (f n)) = fun n => φ (diff h f n) := by
      funext n
      simp [diff]
    rw [he,ih]
    rfl

lemma iterDiff_pair {K : Type*} [Group K] (hs : List A) (f : A → G) (g : A → K) :
    iterDiff hs (fun n => (f n,g n)) = fun n => (iterDiff hs f n,iterDiff hs g n) := by
  induction hs generalizing f g with
  | nil => rfl
  | cons h hs ih => exact ih (diff h f) (diff h g)

 

theorem polynomial_pair (H : Filtration G) (h0 : H.level 0 = ⊤)
    {k : ℕ} {f : A → G} (hf : Polynomial H k f) (t : A) :
    Polynomial (filtration H h0) k (fun n => (f n,f (n+t))) := by
  intro hs n
  rw [iterDiff_pair,iterDiff_shift]
  refine ⟨hf hs n,hf hs (n+t),?_⟩
  have hh := hf (hs++[t]) n
  rw [iterDiff_append] at hh
  simpa [iterDiff,diff,List.length_append,Nat.add_assoc] using hh

lemma iterDiff_left_mul (hs : List A) (hne : hs ≠ []) (a : G) (f : A → G) :
    iterDiff hs (fun n => a*f n) = iterDiff hs f := by
  obtain ⟨h,ts,rfl⟩ := List.exists_cons_of_ne_nil hne
  change iterDiff ts (diff h (fun n => a*f n)) = _
  have he : diff h (fun n => a*f n) = diff h f := by
    funext n
    simp [diff,mul_assoc]
  rw [he]
  rfl

 

def normalizedPair (H : Filtration G) (h0 : H.level 0 = ⊤)
    {f : A → G} (hf : Polynomial H 0 f) (t : A) : A → level H h0 1 := fun n =>
  ⟨(f 0,f t)⁻¹*(f n,f (n+t)), by
    have hh := polynomial_pair H h0 hf t [n] 0
    simpa [iterDiff,diff,filtration] using hh⟩

 
theorem normalizedPair_polynomial (H : Filtration G) (h0 : H.level 0 = ⊤)
    {f : A → G} (hf : Polynomial H 0 f) (t : A) :
    Polynomial (restricted H h0) 0 (normalizedPair H h0 hf t) := by
  intro hs n
  by_cases he : hs = []
  · subst hs
    rw [List.length_nil,add_zero,restricted_zero]
    trivial
  · have hh := polynomial_pair H h0 hf t hs n
    change (↑(iterDiff hs (normalizedPair H h0 hf t) n) : G × G) ∈
      level H h0 (max 1 (0+hs.length))
    have hv := congrFun (iterDiff_hom (level H h0 1).subtype hs
      (normalizedPair H h0 hf t)) n
    simp only [Subgroup.coe_subtype] at hv
    rw [← hv]
    change iterDiff hs (fun n => (f 0,f t)⁻¹*(f n,f (n+t))) n ∈ _
    rw [iterDiff_left_mul hs he]
    have hlen : 1 ≤ hs.length := Nat.succ_le_of_lt (List.length_pos_iff.mpr he)
    simpa only [zero_add, max_eq_right hlen,filtration] using hh

lemma polynomial_map {K : Type*} [Group K] (H : Filtration G) (φ : G →* K)
    {k : ℕ} {f : A → G} (hf : Polynomial H k f) :
    Polynomial (mapFiltration H φ) k (fun n => φ (f n)) := by
  intro hs n
  rw [iterDiff_hom]
  exact ⟨iterDiff hs f n,hf hs n,rfl⟩

 
lemma polynomial_filtered_map {K : Type*} [Group K] (H : Filtration G)
    (J : Filtration K) (φ : G →* K)
    (hφ : ∀ i, (H.level i).map φ ≤ J.level i)
    {k : ℕ} {f : A → G} (hf : Polynomial H k f) :
    Polynomial J k (fun n => φ (f n)) := by
  intro hs n
  rw [iterDiff_hom]
  exact hφ _ ⟨iterDiff hs f n,hf hs n,rfl⟩

 
def restrictedConj (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) (a b : G) : level H h0 1 →* level H h0 1 :=
  ((pairConj a b).toMonoidHom.comp (level H h0 1).subtype).codRestrict _
    (fun x => pairConj_mem H h0 h1 1 a b x.property)

lemma restrictedConj_filtered (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) (a b : G) (i : ℕ) :
    ((restricted H h0).level i).map (restrictedConj H h0 h1 a b) ≤
      (restricted H h0).level i := by
  rintro _ ⟨x,hx,rfl⟩
  exact pairConj_mem H h0 h1 (max 1 i) a b hx

 

theorem normalized_conjugate_polynomial (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) {f : A → G} (hf : Polynomial H 0 f) (t : A) (a b : G) :
    Polynomial (restricted H h0) 0
      (fun n => restrictedConj H h0 h1 a b (normalizedPair H h0 hf t n)) :=
  polynomial_filtered_map _ _ _ (restrictedConj_filtered H h0 h1 a b)
    (normalizedPair_polynomial H h0 hf t)

 

theorem reduced_pair_polynomial (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) {s : ℕ} (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥)
    {f : A → G} (hf : Polynomial H 0 f) (t : A) (a b : G) :
    let R := restricted H h0
    letI := last_normal H h0 hs0 hs
    let π := QuotientGroup.mk' (R.level s)
    let Q := mapFiltration R π
    let p := fun n => π (restrictedConj H h0 h1 a b (normalizedPair H h0 hf t n))
    Polynomial Q 0 p ∧ ∀ hs' : List A, s ≤ hs'.length → ∀ n, iterDiff hs' p n = 1 := by
  let : ((restricted H h0).level s).Normal := last_normal H h0 hs0 hs
  dsimp only
  have hp := polynomial_map (restricted H h0) (QuotientGroup.mk' ((restricted H h0).level s))
    (normalized_conjugate_polynomial H h0 h1 hf t a b)
  refine ⟨hp,?_⟩
  intro ts hts n
  have hh := hp ts n
  have hz : (mapFiltration (restricted H h0)
      (QuotientGroup.mk' ((restricted H h0).level s))).level s = ⊥ :=
    (quotient_lowers_degree H h0 hs0 hs).2.2
  have hmem := (mapFiltration (restricted H h0)
    (QuotientGroup.mk' ((restricted H h0).level s))).antitone
      (by omega : s ≤ 0+ts.length) hh
  simpa only [hz,Subgroup.mem_bot] using hmem

end LeibmanSquare

end
end
end
end

end OAI
