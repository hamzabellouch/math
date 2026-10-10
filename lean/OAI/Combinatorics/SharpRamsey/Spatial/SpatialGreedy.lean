import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialCertificates

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedProjectiveGeometry GreedyPreparation
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialGreedy_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedSpatialGreedy_2 : Fintype (Projectivization K V) := Fintype.ofFinite _
local instance flat_JoinedSpatialGreedy_3 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedSpatialGreedy_4 : Fintype (Submodule K V) := Fintype.ofFinite _

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma complete_members {α β : Type*} {F : Finset β} {U : β→Finset α} {m : ℕ}
    {S : Finset α} {bs : List β} (h : Complete F U m S bs) : ∀ b∈bs,b∈F := by
  induction h with
  | nil => simp
  | cons S b bs hb hr hm ht ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact hb
    · exact ih a ha

omit [Finite K] in
lemma kernel_plane (hdim : Module.finrank K V=4) (f : Module.Dual K V) (hf : f≠0) :
    Module.finrank K (LinearMap.ker f)=3 := by
  have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  omega

lemma filter_kernel (S : Finset (Projectivization K V)) (f : Module.Dual K V) :
    S.filter (fun x => f x.rep=0)=S∩planePoints (LinearMap.ker f) := by
  ext x
  simp only [mem_filter,mem_inter,mem_planePoints,Projectivization.submodule_eq,
    Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]

theorem greedy (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty) (σ g : ℝ)
    (hσ : 0≤σ) (hg : 0≤g) (hN : (S.card:ℝ)=exp (3*σ/2+g)) :
    let m := ⌈exp (σ+17*g/15)⌉₊
    let F := (univ : Finset (Submodule K V)).filter (fun (W : Submodule K V) => Module.finrank K W=3)
    (∃ W : Submodule K V,Module.finrank K W=3 ∧
      (S.card:ℝ)/50≤(S∩planePoints W).card) ∨
    (∃ S' : Finset (Projectivization K V),S'⊆S ∧ S'.Nonempty ∧ S.card≤2*S'.card ∧
      (m:ℝ)≤2*exp (σ+17*g/15) ∧
      (∀ f : Module.Dual K V, f ≠ 0 → (S'.filter (fun x => f x.rep = 0)).card ≤ m)) ∨
    (∃ bs : List (Submodule K V),Complete F (planePoints (K:=K) (V:=V)) m S bs ∧
      (removed S planePoints bs).Nonempty ∧ S.card≤2*(removed S planePoints bs).card ∧
      (bs.length:ℝ)≤exp (σ/2-2*g/15) ∧
      ∀ i : Fin bs.length,((indexedCell (removed S planePoints bs) planePoints bs i).card:ℝ)/
        (removed S planePoints bs).card≤1/25) := by
  dsimp only
  let m := ⌈exp (σ+17*g/15)⌉₊
  let F := (univ : Finset (Submodule K V)).filter (fun (W : Submodule K V) => Module.finrank K W=3)
  have hm0 : 0< m := Nat.ceil_pos.mpr (exp_pos _)
  have hm : exp (σ+17*g/15)≤(m:ℝ) := Nat.le_ceil _
  have hmup : (m:ℝ)≤2*exp (σ+17*g/15) := by
    have hh := Nat.ceil_lt_add_one (exp_pos (σ+17*g/15)).le
    have he : 1≤exp (σ+17*g/15) := one_le_exp_iff.mpr (by linarith)
    change (m:ℝ)<_ at hh
    linarith
  have hSc : 0<S.card := card_pos.mpr hS
  rcases GreedyPreparation.preparation F (planePoints (K:=K) (V:=V)) m hm0 S with ⟨S',hsub,hhalf,hcap⟩|⟨bs,hbs,hhalf,hJ,_⟩
  · right; left
    refine ⟨S',hsub,card_pos.mp (by omega),hhalf,hmup,?_⟩
    intro f hf
    rw [filter_kernel]
    exact (hcap _ (mem_filter.mpr ⟨mem_univ _,kernel_plane hdim f hf⟩)).le
  · have hn : (removed S planePoints bs).Nonempty := card_pos.mp (by omega)
    by_cases hcell : ∀ i : Fin bs.length,((indexedCell (removed S planePoints bs) planePoints bs i).card:ℝ)/
        (removed S planePoints bs).card≤1/25
    · right; right
      refine ⟨bs,hbs,hn,hhalf,?_,hcell⟩
      have hr : (bs.length:ℝ)*(m:ℝ)≤S.card := by exact_mod_cast hJ
      have hmul : (bs.length:ℝ)*exp (σ+17*g/15)≤exp (3*σ/2+g) :=
        (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)).trans (hr.trans_eq hN)
      have he : exp (σ/2-2*g/15)*exp (σ+17*g/15)=exp (3*σ/2+g) := by
        rw [←exp_add]; congr 1; ring
      rw [←he] at hmul
      exact (mul_le_mul_iff_left₀ (exp_pos _)).mp hmul
    · push Not at hcell
      obtain ⟨i,hi⟩ := hcell
      left
      refine ⟨bs[i],(mem_filter.mp (complete_members hbs _ (List.getElem_mem _))).2,?_⟩
      rw [indexedCell_removed] at hi
      have hnc : (0:ℝ)<(removed S planePoints bs).card := by exact_mod_cast card_pos.mpr hn
      have hh := (lt_div_iff₀ hnc).mp hi
      have hh' : (S.card:ℝ)≤2*(removed S planePoints bs).card := by exact_mod_cast hhalf
      have hs : indexedCell S planePoints bs i⊆S∩planePoints bs[i] := by
        dsimp only [indexedCell]
        intro x hx
        exact mem_inter.mpr ⟨residual_subset S planePoints _ (mem_inter.mp hx).1,(mem_inter.mp hx).2⟩
      have hcc : ((indexedCell S planePoints bs i).card:ℝ)≤(S∩planePoints bs[i]).card :=
        Nat.cast_le.mpr (card_le_card hs)
      linarith

end
end SharpLogRamsey.SpatialLearning

end

end OAI
