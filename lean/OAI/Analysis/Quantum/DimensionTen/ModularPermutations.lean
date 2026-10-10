import OAI.Analysis.Quantum.DimensionTen.FrobeniusRoots
import OAI.Analysis.Quantum.DimensionTen.Mod131Result
import OAI.Analysis.Quantum.DimensionTen.Mod139Result
import OAI.Analysis.Quantum.DimensionTen.RootPermutation

namespace OAI

section
noncomputable section
open Equiv Equiv.Perm MulAction
namespace DimensionTen


theorem full_symmetric_of_nineteen_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (H : Subgroup (Perm α)) (hc : Fintype.card α = 20)
    [IsPretransitive H α]
    (σ : Perm α) (hσ : σ ∈ H) (hcycle : σ.IsCycle) (hs : σ.support.card = 19)
    (τ : Perm α) (hτ : τ ∈ H) (hswap : τ.IsSwap) : H = ⊤ := by
  classical
  have ht : (σ.supportᶜ).card = 1 := by rw [Finset.card_compl, hs, hc]
  obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp ht
  have hm (a : α) : σ a ≠ a ↔ a ≠ a₀ := by
    have h := congrArg (fun s : Finset α => a ∈ s) ha₀
    simpa only [Finset.mem_compl, mem_support, not_not, Finset.mem_singleton] using not_congr (iff_of_eq h)
  have hfix : σ a₀ = a₀ := not_ne_iff.mp ((hm a₀).not.mpr (by simp))
  have htwo : IsMultiplyPretransitive H α 2 := by
    rw [is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg⟩ := exists_smul_eq (M := H) a a₀
    obtain ⟨h, hh⟩ := exists_smul_eq (M := H) c a₀
    have hgb : σ (g • b) ≠ g • b := (hm _).mpr (by
      intro hb; exact hab ((MulAction.injective g) (hg.trans hb.symm)))
    have hhd : σ (h • d) ≠ h • d := (hm _).mpr (by
      intro hd; exact hcd ((MulAction.injective h) (hh.trans hd.symm)))
    obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hgb hhd
    refine ⟨h⁻¹ * (⟨σ, hσ⟩ : H) ^ n * g, ?_, ?_⟩
    · simp only [mul_smul, hg]
      have hhfix : ((⟨σ, hσ⟩ : H) ^ n) • a₀ = a₀ := by
        exact pow_apply_eq_self_of_apply_eq_self hfix n
      rw [hhfix, ← hh, inv_smul_smul]
    · simp only [mul_smul]
      change h⁻¹ • ((σ ^ n) (g • b)) = d
      rw [hn, inv_smul_smul]
  exact subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (isPreprimitive_of_is_two_pretransitive htwo) τ hswap hτ

end DimensionTen

end
end

section
noncomputable section
open Polynomial
namespace DimensionTen

lemma root_of_product {k ι : Type*} [Field k] [Fintype ι]
    (r : ι → k) (f : k[X]) (hf : f = ∏ i, (X - C (r i))) (i : ι) :
    f.eval (r i) = 0 := by
  classical
  rw [hf, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

lemma eval_mod131_f {k : Type*} [CommRing k] (x : k) :
    (Mod131.f (X : k[X])).eval x = Mod131.f x :=
  (Mod131.map_f (evalRingHom x) X).trans (congrArg Mod131.f (eval_X))

lemma eval_mod131_g {k : Type*} [CommRing k] (x : k) :
    (Mod131.g17 (X : k[X])).eval x = Mod131.g17 x :=
  (Mod131.map_g17 (evalRingHom x) X).trans (congrArg Mod131.g17 (eval_X))

lemma fixed_mod131 {k ι : Type*} [Field k] [CharP k 131] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
    (hfact : Mod131.f X = ∏ i, (X - C (r i)))
    (hfrob : ∀ i, r (π i) = r i ^ 131) :
    Fintype.card {i : ι // (π ^ 17) i = i} = 18 := by
  have hfroot (i : ι) : Mod131.f (r i) = 0 := by
    rw [← eval_mod131_f]; exact root_of_product r _ hfact i
  have hfix (i : ι) : (Mod131.g17 (X : k[X])).eval (r i) = 0 ↔ (π ^ 17) i = i := by
    rw [eval_mod131_g, ← Mod131.fixed_iff_g_zero _ (hfroot i),
      ← iterate_pow_perm π r 131 hfrob 17 i, hinj.eq_iff]
  have hd : Mod131.g17 (X : k[X]) ∣ Mod131.f X :=
    ⟨Mod131.div17_f X, Mod131.factor17_f X⟩
  exact (card_fixed_of_factor r hinj (π ^ 17) _ _ hfact Mod131.separable_f hd hfix).trans
    Mod131.degree_g.natDegree_eq

lemma eval_mod139_f {k : Type*} [CommRing k] (x : k) :
    (Mod139.f (X : k[X])).eval x = Mod139.f x :=
  (Mod139.map_f (evalRingHom x) X).trans (congrArg Mod139.f (eval_X))

lemma eval_mod139_g {k : Type*} [CommRing k] (x : k) :
    (Mod139.g1 (X : k[X])).eval x = Mod139.g1 x :=
  (Mod139.map_g1 (evalRingHom x) X).trans (congrArg Mod139.g1 (eval_X))

lemma fixed_mod139 {k ι : Type*} [Field k] [CharP k 139] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
    (hfact : Mod139.f X = ∏ i, (X - C (r i)))
    (hfrob : ∀ i, r (π i) = r i ^ 139) :
    Fintype.card {i : ι // (π ^ 1) i = i} = 1 := by
  have hfroot (i : ι) : Mod139.f (r i) = 0 := by
    rw [← eval_mod139_f]; exact root_of_product r _ hfact i
  have hfix (i : ι) : (Mod139.g1 (X : k[X])).eval (r i) = 0 ↔ (π ^ 1) i = i := by
    rw [eval_mod139_g, ← Mod139.fixed_iff_g_zero _ (hfroot i),
      ← iterate_pow_perm π r 139 hfrob 1 i, hinj.eq_iff]
  have hd : Mod139.g1 (X : k[X]) ∣ Mod139.f X :=
    ⟨Mod139.div1_f X, Mod139.factor1_f X⟩
  exact (card_fixed_of_factor r hinj (π ^ 1) _ _ hfact Mod139.separable_f hd hfix).trans
    Mod139.degree_g.natDegree_eq

lemma pow_mod139 {k ι : Type*} [Field k] [CharP k 139] [Fintype ι]
    (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
    (hfact : Mod139.f X = ∏ i, (X - C (r i)))
    (hfrob : ∀ i, r (π i) = r i ^ 139) : π ^ 19 = 1 := by
  ext i
  apply hinj
  rw [iterate_pow_perm π r 139 hfrob]
  have hr : Mod139.f (r i) = 0 := by
    rw [← eval_mod139_f]; exact root_of_product r _ hfact i
  rw [Mod139.iterate19 _ hr]
  
  simp [Mod139.u19, Mod139.u0]

end DimensionTen

end
end

end OAI
