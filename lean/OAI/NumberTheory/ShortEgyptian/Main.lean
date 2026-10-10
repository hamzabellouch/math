import OAI.NumberTheory.ShortEgyptian.UpperAssembly

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Finset Filter Topology

lemma eventually_upper_at_scale : ∀ᶠ S : ℝ in atTop, ∀ a b : ℕ, 1≤a → a<b → (b:ℝ)=Real.exp S →
    ∃ ns, IsExpansion a b ns ∧ (ns.length:ℝ)≤upperConstant*Real.log S := by
  filter_upwards [eventually_density,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with S hd hS hlog
  intro a b ha hab hb
  exact upper_at_scale S hS hlog hd a b ha hab hb

theorem main_upper_expansions : ∃ b₀ : ℕ, 2≤b₀ ∧ ∀ b : ℕ, b₀≤b → ∀ a : ℕ, 1≤a → a<b →
    ∃ ns, IsExpansion a b ns ∧ (ns.length:ℝ)≤upperConstant*Real.log (Real.log (b:ℝ)) := by
  obtain ⟨S₀,hS₀⟩ := eventually_atTop.mp eventually_upper_at_scale
  let b₀ := max 2 ⌈Real.exp S₀⌉₊
  refine ⟨b₀,le_max_left _ _,?_⟩
  intro b hb a ha hab
  have hb2 : 2≤b := (le_max_left _ _).trans hb
  have hbp : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hbexp : Real.exp S₀ ≤ (b:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hb))
  have hlog : S₀ ≤ Real.log b := by
    have hh := Real.log_le_log (Real.exp_pos S₀) hbexp
    simpa only [Real.log_exp] using hh
  exact hS₀ (Real.log b) hlog a b ha hab (Real.exp_log hbp).symm

theorem main :
    (∀ a b : ℕ, 1 ≤ a → a < b → ∃ ns : List ℕ, IsExpansion a b ns) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ b : ℕ, b₀ ≤ b →
        c₁ * Real.log (Real.log (b : ℝ)) ≤ (maxMinLength b : ℝ) ∧
        (maxMinLength b : ℝ) ≤ c₂ * Real.log (Real.log (b : ℝ)) := by
  refine ⟨fun a b _ hab => exists_expansion a b hab,1/2,upperConstant,by norm_num,upperConstant_pos,?_⟩
  obtain ⟨b₀,hb₀,hupper⟩ := main_upper_expansions
  refine ⟨b₀,hb₀,?_⟩
  intro b hb
  have hb2 : 2≤b := hb₀.trans hb
  refine ⟨main_lower b hb2,?_⟩
  have hne : (Ico 1 b).Nonempty := ⟨1,mem_Ico.mpr ⟨le_rfl,by omega⟩⟩
  obtain ⟨a,ha,heq⟩ := exists_mem_eq_sup (Ico 1 b) hne (fun a => minLength a b)
  obtain ⟨ha,hab⟩ := mem_Ico.mp ha
  obtain ⟨ns,hns,hlen⟩ := hupper b hb a ha hab
  have hh : (minLength a b:ℝ)≤ns.length := by exact_mod_cast minLength_le hns
  have hmax : maxMinLength b=minLength a b := heq
  rw [hmax]
  exact hh.trans hlen

end ShortEgyptian

end OAI
