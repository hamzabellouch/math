import OAI.Analysis.AncientFlat.Regularity.ClassicalHolder
import OAI.Analysis.AncientFlat.Evolution.SourceEvolution

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
open ParametrixVolterra FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}
lemma exists_holder_source_evolves (hα : 0<α) (L B : ℝ) (hL : 0≤L) (hB : 0≤B)
    (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (R : ℝ) (hR0 : 0≤R) (hR : R≤1)
    (hb : ∀ s ∈ Icc 0 R, ‖b s‖≤B)
    (hLip : ∀ s ∈ Icc 0 R, ∀ r ∈ Icc 0 R, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s-r|))
    (hLipb : ∀ s ∈ Icc 0 R, ∀ x z : V, ‖b s x-b s z‖≤L*‖x-z‖)
    (hA : ∀ s ∈ Icc 0 R, ContDiff ℝ ∞ (fun x => (A s x).val))
    (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc 0 R, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ)
    (d : C₀(V,ℂ)) : ∃ u : ℝ → C₀(V,ℂ), SourceEvolves A b f 0 R d u ∧
      (∀ a : ℝ, 0<a → ∃ C : ℝ, 0≤C ∧
        (∀ t∈Icc a R, ∀ x, ‖iteratedFDeriv ℝ 4 (fun y => u t y) x‖≤C) ∧
        (∀ t∈Icc a R, ∀ s∈Icc a R, ∀ x y,
          ‖iteratedFDeriv ℝ 4 (fun z => u t z) x-iteratedFDeriv ℝ 4 (fun z => u s z) y‖≤
            C*(‖x-y‖^γ+|t-s|^(γ/4)))) := by
  let incl : C(Slab R,ℝ) := ⟨Subtype.val,continuous_subtype_val⟩
  let l : Time R →ᵇ C₀(V,ℂ) := f.compContinuous ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨K,hK,hs⟩ := exists_classical_holder_source_evolution hα (A.comp incl) (b.comp incl)
    hR0 hR L B hL hB (fun r => hb r.val r.property)
    (fun s r x z => hLip s.val s.property r.val r.property x z)
    (fun s x z => hLipb s.val s.property x z) (fun s => hA s.val s.property)
  obtain ⟨H,hH,hf⟩ := hf
  obtain ⟨u,hu0,huc,_,huJ,huB,hut,huH⟩ := hs γ hγ hγ1 d l
    ⟨H,hH,fun t x y => hf t.val ⟨t.property.1.le,t.property.2⟩ x y⟩
  exact ⟨u,⟨hu0,huc,huJ,huB,fun t ht => hut ⟨t,ht.1,ht.2.le⟩ ht.2⟩,huH⟩

lemma SourceEvolves.fourth_holder (hα : 0<α) (L B C : ℝ) (hL : 0≤L) (hB : 0≤B) (hC : 0≤C)
    (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (R : ℝ) (hR0 : 0≤R) (hR : R≤1)
    (hb : ∀ s ∈ Icc 0 R, ‖b s‖≤B)
    (hLip : ∀ s ∈ Icc 0 R, ∀ r ∈ Icc 0 R, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s-r|))
    (hLipb : ∀ s ∈ Icc 0 R, ∀ x z : V, ‖b s x-b s z‖≤L*‖x-z‖)
    (hA : ∀ s ∈ Icc 0 R, ContDiff ℝ ∞ (fun x => (A s x).val))
    (hAj : ∀ t ∈ Icc 0 R, ∀ n : ℕ, n≤2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A t y).val) x‖≤C)
    (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc 0 R, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ)
    (d : C₀(V,ℂ)) (u : ℝ → C₀(V,ℂ)) (hu : SourceEvolves A b f 0 R d u) :
      ∀ a : ℝ, 0<a → ∃ C : ℝ, 0≤C ∧
        (∀ t∈Icc a R, ∀ x, ‖iteratedFDeriv ℝ 4 (fun y => u t y) x‖≤C) ∧
        (∀ t∈Icc a R, ∀ s∈Icc a R, ∀ x y,
          ‖iteratedFDeriv ℝ 4 (fun z => u t z) x-iteratedFDeriv ℝ 4 (fun z => u s z) y‖≤
            C*(‖x-y‖^γ+|t-s|^(γ/4))) := by
  obtain ⟨w,hw,hwH⟩ := exists_holder_source_evolves hα L B hL hB A b R hR0 hR hb hLip hLipb hA γ hγ hγ1 f hf d
  have he := hu.unique hw hR0 hα hC hB hb (fun t ht => (hA t ht).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))) hAj
  intro a ha
  obtain ⟨M,hM,hM0,hM1⟩ := hwH a ha
  have hm (t : ℝ) (ht : t ∈ Icc a R) : t∈Icc 0 R := ⟨ha.le.trans ht.1,ht.2⟩
  refine ⟨M,hM,fun t ht x => ?_,fun t ht s hs x y => ?_⟩
  · rw [he t (hm t ht)]
    exact hM0 t ht x
  · rw [he t (hm t ht),he s (hm s hs)]
    exact hM1 t ht s hs x y
end ParametrixEvolution

end

end OAI
