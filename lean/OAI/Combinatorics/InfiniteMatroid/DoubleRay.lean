import OAI.Combinatorics.InfiniteMatroid.Basic

namespace OAI

section
open Set Matroid
namespace InfiniteMatroidCounterexample

/-- Inward (false) and outward (true) bundles with the central edge at -1. -/
def bundleAt (n : ℤ) (b : Bool) : ℤ :=
  if n < 0 then (if b then n - 1 else n) else (if b then n else n - 1)

lemma bundleAt_bounds (n : ℤ) (b : Bool) : n - 1 ≤ bundleAt n b ∧ bundleAt n b ≤ n := by
  unfold bundleAt
  split_ifs <;> omega
lemma bundleAt_injective (n : ℤ) : Function.Injective (bundleAt n) := by
  intro b c h
  cases b <;> cases c <;> simp_all [bundleAt] <;> split_ifs at h <;> omega
lemma bundleAt_right (n : ℤ) : ∃ b, bundleAt n b = n := by
  by_cases h : n < 0
  · exact ⟨false,by simp [bundleAt,h]⟩
  · exact ⟨true,by simp [bundleAt,h]⟩
lemma bundleAt_left (n : ℤ) : ∃ b, bundleAt n b = n - 1 := by
  by_cases h : n < 0
  · exact ⟨true,by simp [bundleAt,h]⟩
  · exact ⟨false,by simp [bundleAt,h]⟩

def parityBit (p : Bool) : ℤ := if p then 1 else 0
abbrev Vertex (p : Bool) := {n : ℤ // n % 2 = parityBit p}

def componentMap {α : Type*} {p : Bool} (v : Vertex p) (x : α × Bool) : ℤ × α :=
  (bundleAt v x.2,x.1)

def globalComponentMap (α : Type*) (p : Bool) (x : Vertex p × (α × Bool)) : ℤ × α :=
  componentMap x.1 x.2

lemma globalComponentMap_injective (α : Type*) (p : Bool) :
    Function.Injective (globalComponentMap α p) := by
  rintro ⟨⟨n,hn⟩,d,b⟩ ⟨⟨m,hm⟩,e,c⟩ h
  have hnm : bundleAt n b = bundleAt m c := congrArg Prod.fst h
  have hde : d = e := congrArg Prod.snd h
  have hb := bundleAt_bounds n b
  have hc := bundleAt_bounds m c
  have hnm' : n = m := by omega
  subst m
  have hbc := bundleAt_injective n hnm
  subst e; subst c
  rfl

lemma globalComponentMap_surjective (α : Type*) (p : Bool) :
    Function.Surjective (globalComponentMap α p) := by
  rintro ⟨n,d⟩
  by_cases hn : n % 2 = parityBit p
  · obtain ⟨b,hb⟩ := bundleAt_right n
    exact ⟨(⟨n,hn⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
  · have hn' : (n+1) % 2 = parityBit p := by
      cases p <;> simp only [parityBit,Bool.false_eq_true,ite_false,ite_true] at hn ⊢ <;> omega
    obtain ⟨b,hb⟩ := bundleAt_left (n+1)
    exact ⟨(⟨n+1,hn'⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩

noncomputable def componentEquiv (α : Type*) (p : Bool) : (Vertex p × (α × Bool)) ≃ (ℤ × α) :=
  Equiv.ofBijective (globalComponentMap α p) (by
    have bundleAt_bounds (n : ℤ) (b : Bool) : n - 1 ≤ bundleAt n b ∧ bundleAt n b ≤ n := by
      unfold bundleAt
      split_ifs <;> omega
    have bundleAt_injective (n : ℤ) : Function.Injective (bundleAt n) := by
      intro b c h
      cases b <;> cases c <;> simp_all [bundleAt] <;> split_ifs at h <;> omega
    have bundleAt_right (n : ℤ) : ∃ b, bundleAt n b = n := by
      by_cases h : n < 0
      · exact ⟨false,by simp [bundleAt,h]⟩
      · exact ⟨true,by simp [bundleAt,h]⟩
    have bundleAt_left (n : ℤ) : ∃ b, bundleAt n b = n - 1 := by
      by_cases h : n < 0
      · exact ⟨true,by simp [bundleAt,h]⟩
      · exact ⟨false,by simp [bundleAt,h]⟩

    have globalComponentMap_injective :
        Function.Injective (globalComponentMap α p) := by
      rintro ⟨⟨n,hn⟩,d,b⟩ ⟨⟨m,hm⟩,e,c⟩ h
      have hnm : bundleAt n b = bundleAt m c := congrArg Prod.fst h
      have hde : d = e := congrArg Prod.snd h
      have hb := bundleAt_bounds n b
      have hc := bundleAt_bounds m c
      have hnm' : n = m := by omega
      subst m
      have hbc := bundleAt_injective n hnm
      subst e; subst c
      rfl

    have globalComponentMap_surjective :
        Function.Surjective (globalComponentMap α p) := by
      rintro ⟨n,d⟩
      by_cases hn : n % 2 = parityBit p
      · obtain ⟨b,hb⟩ := bundleAt_right n
        exact ⟨(⟨n,hn⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
      · have hn' : (n+1) % 2 = parityBit p := by
          cases p <;> simp only [parityBit,Bool.false_eq_true,ite_false,ite_true] at hn ⊢ <;> omega
        obtain ⟨b,hb⟩ := bundleAt_left (n+1)
        exact ⟨(⟨n+1,hn'⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
    exact ⟨globalComponentMap_injective, globalComponentMap_surjective⟩)

noncomputable def rayMatroid {α : Type*} (Q : Matroid (α × Bool)) (p : Bool) : Matroid (ℤ × α) :=
  (Matroid.sum' (fun _ : Vertex p ↦ Q)).mapEquiv (componentEquiv α p)

lemma rayMatroid_ground {α : Type*} (Q : Matroid (α × Bool)) (hQ : Q.E = univ) (p : Bool) :
    (rayMatroid Q p).E = univ := by
  have hg : (Matroid.sum' (fun _ : Vertex p ↦ Q)).E = univ := by
    ext ⟨v,x⟩
    simp only [Matroid.sum'_ground_eq,hQ,mem_iUnion,mem_image,mem_univ,true_and,iff_true]
    exact ⟨v,x,rfl⟩
  rw [rayMatroid,Matroid.mapEquiv_ground_eq,hg]
  rw [Set.image_univ]
  exact Set.range_eq_univ.mpr (componentEquiv α p).surjective

lemma rayMatroid_indep_iff {α : Type*} (Q : Matroid (α × Bool)) (p : Bool) (I : Set (ℤ × α)) :
    (rayMatroid Q p).Indep I ↔ ∀ v : Vertex p, Q.Indep (componentMap v ⁻¹' I) := by
  rw [rayMatroid,Matroid.mapEquiv_indep_iff,Equiv.image_symm_eq_preimage,Matroid.sum'_indep_iff]
  rfl
lemma rayMatroid_isBase_iff {α : Type*} (Q : Matroid (α × Bool)) (p : Bool) (B : Set (ℤ × α)) :
    (rayMatroid Q p).IsBase B ↔ ∀ v : Vertex p, Q.IsBase (componentMap v ⁻¹' B) := by
  rw [rayMatroid,Matroid.mapEquiv_isBase_iff,Equiv.image_symm_eq_preimage,Matroid.sum'_isBase_iff]
  rfl

lemma selfDual_compl_base_iff {α : Type*} (Q : Matroid α) (hE : Q.E = univ) (hQ : Q.dual = Q)
    (B : Set α) : Q.IsBase Bᶜ ↔ Q.IsBase B := by
  have h : Q.dual.IsBase B ↔ Q.IsBase Bᶜ := by
    rw [Matroid.dual_isBase_iff,hE,←Set.compl_eq_univ_sdiff]
  rw [hQ] at h
  exact h.symm

lemma rayMatroid_selfDual {α : Type*} (Q : Matroid (α × Bool)) (hE : Q.E = univ) (hQ : Q.dual = Q)
    (p : Bool) : (rayMatroid Q p).dual = rayMatroid Q p := by
  apply Matroid.ext_isBase Matroid.dual_ground
  intro B _
  rw [Matroid.dual_isBase_iff,rayMatroid_ground Q hE,←Set.compl_eq_univ_sdiff,
    rayMatroid_isBase_iff,rayMatroid_isBase_iff]
  exact forall_congr' (fun v ↦ selfDual_compl_base_iff Q hE hQ (componentMap v ⁻¹' B))

/-- The independent partition is assigned to vertices by parity. -/
def assignment {α : Type*} (I : Set (ℤ × α)) (n : ℤ) : Set (α × Bool) :=
  {x | if n % 2 = 0 then (bundleAt n x.2,x.1) ∈ I else (bundleAt n x.2,x.1) ∉ I}

lemma assignment_indep {α : Type*} (Q : Matroid (α × Bool)) {I : Set (ℤ × α)}
    (h0 : (rayMatroid Q false).Indep I) (h1 : (rayMatroid Q true).Indep Iᶜ) (n : ℤ) :
    Q.Indep (assignment I n) := by
  by_cases hn : n % 2 = 0
  · have hv : n % 2 = parityBit false := hn
    have hi := (rayMatroid_indep_iff Q false I).mp h0 ⟨n,hv⟩
    change Q.Indep {x | (bundleAt n x.2,x.1) ∈ I} at hi
    simpa only [assignment,hn,ite_true] using hi
  · have hv : n % 2 = parityBit true := by change n % 2 = 1; omega
    have hi := (rayMatroid_indep_iff Q true Iᶜ).mp h1 ⟨n,hv⟩
    change Q.Indep {x | (bundleAt n x.2,x.1) ∉ I} at hi
    simpa only [assignment,hn,ite_false] using hi

end InfiniteMatroidCounterexample
end

end OAI
