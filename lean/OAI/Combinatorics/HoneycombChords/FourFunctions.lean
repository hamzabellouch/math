import Mathlib

namespace OAI

/-!
# Four-functions inequalities for ordered real vectors

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section

/-! A continuous four-functions inequality on bounded sublattices. -/
namespace Honeycomb370
open MeasureTheory Filter Set
open scoped Topology Pointwise

private def rationalGrid {ι : Type*} [Fintype ι] (n : ℕ) [NeZero n] :
    Sublattice (ι → ℝ) where
  carrier := (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  supClosed' := by
    intro x hx y hy
    rw [← Submodule.coe_pointwise_smul] at hx hy ⊢
    have hx := (BoxIntegral.unitPartition.mem_smul_span_iff (n := n) (v := x)).mp hx
    have hy := (BoxIntegral.unitPartition.mem_smul_span_iff (n := n) (v := y)).mp hy
    apply (BoxIntegral.unitPartition.mem_smul_span_iff (n := n)).mpr
    intro i
    rcases le_total (x i) (y i) with h | h
    · simpa [Pi.sup_apply, max_eq_right h] using hy i
    · simpa [Pi.sup_apply, max_eq_left h] using hx i
  infClosed' := by
    intro x hx y hy
    rw [← Submodule.coe_pointwise_smul] at hx hy ⊢
    have hx := (BoxIntegral.unitPartition.mem_smul_span_iff (n := n) (v := x)).mp hx
    have hy := (BoxIntegral.unitPartition.mem_smul_span_iff (n := n) (v := y)).mp hy
    apply (BoxIntegral.unitPartition.mem_smul_span_iff (n := n)).mpr
    intro i
    rcases le_total (x i) (y i) with h | h
    · simpa [Pi.inf_apply, min_eq_left h] using hx i
    · simpa [Pi.inf_apply, min_eq_right h] using hy i

theorem continuous_four_functions {ι : Type*} [Fintype ι]
    (S : Sublattice (ι → ℝ)) (hs₁ : Bornology.IsBounded (S : Set (ι → ℝ)))
    (hs₂ : MeasurableSet (S : Set (ι → ℝ)))
    (hs₃ : volume (frontier (S : Set (ι → ℝ))) = 0)
    (f₁ f₂ f₃ f₄ : (ι → ℝ) → ℝ)
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂)
    (hc₃ : Continuous f₃) (hc₄ : Continuous f₄)
    (h₁ : ∀ x ∈ S, 0 ≤ f₁ x) (h₂ : ∀ x ∈ S, 0 ≤ f₂ x)
    (h₃ : ∀ x ∈ S, 0 ≤ f₃ x) (h₄ : ∀ x ∈ S, 0 ≤ f₄ x)
    (h : ∀ x ∈ S, ∀ y ∈ S, f₁ x * f₂ y ≤ f₃ (x ⊓ y) * f₄ (x ⊔ y)) :
    (∫ x in (S : Set (ι → ℝ)), f₁ x) * (∫ x in (S : Set (ι → ℝ)), f₂ x) ≤
      (∫ x in (S : Set (ι → ℝ)), f₃ x) * (∫ x in (S : Set (ι → ℝ)), f₄ x) := by
  have lim₁ := tendsto_tsum_div_pow_atTop_integral (S : Set (ι → ℝ)) f₁ hc₁ hs₁ hs₂ hs₃
  have lim₂ := tendsto_tsum_div_pow_atTop_integral (S : Set (ι → ℝ)) f₂ hc₂ hs₁ hs₂ hs₃
  have lim₃ := tendsto_tsum_div_pow_atTop_integral (S : Set (ι → ℝ)) f₃ hc₃ hs₁ hs₂ hs₃
  have lim₄ := tendsto_tsum_div_pow_atTop_integral (S : Set (ι → ℝ)) f₄ hc₄ hs₁ hs₂ hs₃
  refine le_of_tendsto_of_tendsto (lim₁.mul lim₂) (lim₃.mul lim₄) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let T := S ⊓ rationalGrid (ι := ι) n
  have hT : (T : Set (ι → ℝ)).Finite := by
    change ((S : Set (ι → ℝ)) ∩ (n : ℝ)⁻¹ •
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).Finite
    rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]
    exact ZSpan.setFinite_inter _ hs₁
  let _ : Fintype T := hT.fintype
  have ff := four_functions_theorem_univ
    (fun x : T ↦ f₁ x) (fun x : T ↦ f₂ x)
    (fun x : T ↦ f₃ x) (fun x : T ↦ f₄ x)
    (fun x ↦ h₁ x x.property.1) (fun x ↦ h₂ x x.property.1)
    (fun x ↦ h₃ x x.property.1) (fun x ↦ h₄ x x.property.1)
    (fun x y ↦ h x x.property.1 y y.property.1)
  change (∑' x : T, f₁ x) / (n : ℝ) ^ Fintype.card ι *
      ((∑' x : T, f₂ x) / (n : ℝ) ^ Fintype.card ι) ≤
    (∑' x : T, f₃ x) / (n : ℝ) ^ Fintype.card ι *
      ((∑' x : T, f₄ x) / (n : ℝ) ^ Fintype.card ι)
  simp only [tsum_fintype, div_mul_div_comm]
  exact div_le_div_of_nonneg_right ff (mul_self_nonneg _)
end Honeycomb370

end


section

namespace Honeycomb370
open Set MeasureTheory

/-- Closed truncations of the actual ordered positive-node chamber. -/
def orderedBox (n : ℕ) (a b : ℝ) : Sublattice (Fin n → ℝ) where
  carrier := {x | Monotone x ∧ ∀ i,a≤x i ∧ x i≤b}
  supClosed' := by
    rintro x ⟨hx,hxb⟩ y ⟨hy,hyb⟩
    refine ⟨fun i j hij ↦ max_le_max (hx hij) (hy hij),fun i ↦ ?_⟩
    exact ⟨(hxb i).1.trans (le_max_left _ _),max_le (hxb i).2 (hyb i).2⟩
  infClosed' := by
    rintro x ⟨hx,hxb⟩ y ⟨hy,hyb⟩
    refine ⟨fun i j hij ↦ min_le_min (hx hij) (hy hij),fun i ↦ ?_⟩
    exact ⟨le_min (hxb i).1 (hyb i).1,(min_le_left _ _).trans (hxb i).2⟩

lemma orderedBox_closed (n : ℕ) (a b : ℝ) :
    IsClosed (orderedBox n a b : Set (Fin n → ℝ)) := by
  change IsClosed {x | Monotone x ∧ ∀ i,a≤x i ∧ x i≤b}
  apply IsClosed.inter
  · change IsClosed {x : Fin n → ℝ | ∀ (i j : Fin n),i≤j → x i≤x j}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦ isClosed_iInter
      (fun _ ↦ isClosed_le (continuous_apply i) (continuous_apply j))))
  · change IsClosed {x : Fin n → ℝ | ∀ i,a≤x i ∧ x i≤b}
    simp only [Set.ofPred_forall,Set.ofPred_and]
    exact isClosed_iInter (fun i ↦ (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const))

lemma orderedBox_bounded (n : ℕ) (a b : ℝ) :
    Bornology.IsBounded (orderedBox n a b : Set (Fin n → ℝ)) := by
  apply (isCompact_Icc (a:=fun _ : Fin n ↦ a) (b:=fun _ ↦ b)).isBounded.subset
  intro x hx
  exact ⟨fun i ↦ (hx.2 i).1,fun i ↦ (hx.2 i).2⟩

lemma orderedBox_convex (n : ℕ) (a b : ℝ) :
    Convex ℝ (orderedBox n a b : Set (Fin n → ℝ)) := by
  intro x hx y hy u v hu hv huv
  refine ⟨?_,?_⟩
  · intro i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.1 hij) hu)
      (mul_le_mul_of_nonneg_left (hy.1 hij) hv)
  · intro i
    constructor
    · have hl:=add_le_add (mul_le_mul_of_nonneg_left (hx.2 i).1 hu)
        (mul_le_mul_of_nonneg_left (hy.2 i).1 hv)
      change a≤u*x i+v*y i
      nlinarith [hl,congrArg (fun t : ℝ ↦ t*a) huv]
    · have hl:=add_le_add (mul_le_mul_of_nonneg_left (hx.2 i).2 hu)
        (mul_le_mul_of_nonneg_left (hy.2 i).2 hv)
      change u*x i+v*y i≤b
      nlinarith [hl,congrArg (fun t : ℝ ↦ t*b) huv]

lemma orderedBox_four_functions (n : ℕ) (a b : ℝ)
    (f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ)
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂)
    (hc₃ : Continuous f₃) (hc₄ : Continuous f₄)
    (h₁ : ∀ x∈orderedBox n a b,0≤f₁ x) (h₂ : ∀ x∈orderedBox n a b,0≤f₂ x)
    (h₃ : ∀ x∈orderedBox n a b,0≤f₃ x) (h₄ : ∀ x∈orderedBox n a b,0≤f₄ x)
    (h : ∀ x∈orderedBox n a b,∀ y∈orderedBox n a b,
      f₁ x*f₂ y≤f₃ (x⊓y)*f₄ (x⊔y)) :
    (∫ x in (orderedBox n a b : Set (Fin n → ℝ)),f₁ x)*
      (∫ x in (orderedBox n a b : Set (Fin n → ℝ)),f₂ x) ≤
    (∫ x in (orderedBox n a b : Set (Fin n → ℝ)),f₃ x)*
      (∫ x in (orderedBox n a b : Set (Fin n → ℝ)),f₄ x) := by
  exact continuous_four_functions (orderedBox n a b) (orderedBox_bounded n a b)
    (orderedBox_closed n a b).measurableSet ((orderedBox_convex n a b).addHaar_frontier volume)
    f₁ f₂ f₃ f₄ hc₁ hc₂ hc₃ hc₄ h₁ h₂ h₃ h₄ h

end Honeycomb370

end


section

namespace Honeycomb370
open MeasureTheory Set Filter Topology

lemma continuousOn_closed_extension {d : ℕ} {S : Set (Fin d → ℝ)}
    (hs : IsClosed S) (f : (Fin d → ℝ) → ℝ) (hc : ContinuousOn f S) :
    ∃ g : (Fin d → ℝ) → ℝ,Continuous g ∧ EqOn g f S := by
  obtain ⟨g,hg⟩ := ContinuousMap.exists_restrict_eq hs
    (⟨fun x : S ↦ f x,hc.domRestrict⟩ : C(S,ℝ))
  refine ⟨g,g.continuous,?_⟩
  intro x hx
  exact congrArg (fun k : C(S,ℝ) ↦ k ⟨x,hx⟩) hg

lemma orderedBox_continuousOn_four_functions (n : ℕ) (a b : ℝ)
    (f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ)
    (hc₁ : ContinuousOn f₁ (orderedBox n a b)) (hc₂ : ContinuousOn f₂ (orderedBox n a b))
    (hc₃ : ContinuousOn f₃ (orderedBox n a b)) (hc₄ : ContinuousOn f₄ (orderedBox n a b))
    (h₁ : ∀ x∈orderedBox n a b,0≤f₁ x) (h₂ : ∀ x∈orderedBox n a b,0≤f₂ x)
    (h₃ : ∀ x∈orderedBox n a b,0≤f₃ x) (h₄ : ∀ x∈orderedBox n a b,0≤f₄ x)
    (h : ∀ x∈orderedBox n a b,∀ y∈orderedBox n a b,
      f₁ x*f₂ y≤f₃ (x⊓y)*f₄ (x⊔y)) :
    (∫ x in (orderedBox n a b : Set (Fin n → ℝ)),f₁ x)*
      (∫ x in (orderedBox n a b : Set (Fin n → ℝ)),f₂ x) ≤
    (∫ x in (orderedBox n a b : Set (Fin n → ℝ)),f₃ x)*
      (∫ x in (orderedBox n a b : Set (Fin n → ℝ)),f₄ x) := by
  obtain ⟨g₁,hg₁,he₁⟩:=continuousOn_closed_extension (orderedBox_closed n a b) f₁ hc₁
  obtain ⟨g₂,hg₂,he₂⟩:=continuousOn_closed_extension (orderedBox_closed n a b) f₂ hc₂
  obtain ⟨g₃,hg₃,he₃⟩:=continuousOn_closed_extension (orderedBox_closed n a b) f₃ hc₃
  obtain ⟨g₄,hg₄,he₄⟩:=continuousOn_closed_extension (orderedBox_closed n a b) f₄ hc₄
  have hh:=orderedBox_four_functions n a b g₁ g₂ g₃ g₄ hg₁ hg₂ hg₃ hg₄
    (fun x hx ↦ by rw [he₁ hx]; exact h₁ x hx)
    (fun x hx ↦ by rw [he₂ hx]; exact h₂ x hx)
    (fun x hx ↦ by rw [he₃ hx]; exact h₃ x hx)
    (fun x hx ↦ by rw [he₄ hx]; exact h₄ x hx)
    (fun x hx y hy ↦ by
      rw [he₁ hx,he₂ hy,he₃ ((orderedBox n a b).inf_mem hx hy),
        he₄ ((orderedBox n a b).sup_mem hx hy)]
      exact h x hx y hy)
  rwa [setIntegral_congr_fun (orderedBox_closed n a b).measurableSet (fun x hx ↦ he₁ hx),
    setIntegral_congr_fun (orderedBox_closed n a b).measurableSet (fun x hx ↦ he₂ hx),
    setIntegral_congr_fun (orderedBox_closed n a b).measurableSet (fun x hx ↦ he₃ hx),
    setIntegral_congr_fun (orderedBox_closed n a b).measurableSet (fun x hx ↦ he₄ hx)] at hh

def orderedPositive (n : ℕ) : Set (Fin n → ℝ) :=
  {x | Monotone x ∧ ∀ i,0<x i}

lemma orderedPositive_eq_iUnion (n : ℕ) : orderedPositive n =
    ⋃ m : ℕ,(orderedBox n (1/((m:ℝ)+1)) ((m:ℝ)+1) : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · rintro ⟨hx,hx0⟩
    have hev : ∀ᶠ m : ℕ in atTop,∀ i,1/((m:ℝ)+1)≤x i ∧ x i≤(m:ℝ)+1 := by
      apply Filter.eventually_all.mpr
      intro i
      have h₁ := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually
        (gt_mem_nhds (hx0 i))
      have h₂ := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (x i))
      filter_upwards [h₁,h₂] with m hm₁ hm₂
      exact ⟨hm₁.le,by linarith⟩
    obtain ⟨m,hm⟩:=hev.exists
    exact mem_iUnion.mpr ⟨m,hx,hm⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨m,hm⟩
    refine ⟨hm.1,fun i ↦ ?_⟩
    exact (by positivity : (0:ℝ)<1/((m:ℝ)+1)).trans_le (hm.2 i).1

lemma orderedBox_exhaust_monotone (n : ℕ) :
    Monotone (fun m : ℕ ↦ (orderedBox n (1/((m:ℝ)+1)) ((m:ℝ)+1) : Set (Fin n → ℝ))) := by
  intro m k hmk x hx
  refine ⟨hx.1,fun i ↦ ⟨?_,?_⟩⟩
  · exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmk 1)).trans (hx.2 i).1
  · exact (hx.2 i).2.trans (by exact_mod_cast Nat.add_le_add_right hmk 1)

/-- Continuous four-functions inequality on the unbounded actual ordered
positive-node chamber. Integrability is a pairing-domain obligation, not an
association assumption. -/
theorem orderedPositive_four_functions (n : ℕ)
    (f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ)
    (hc₁ : ContinuousOn f₁ (orderedPositive n)) (hc₂ : ContinuousOn f₂ (orderedPositive n))
    (hc₃ : ContinuousOn f₃ (orderedPositive n)) (hc₄ : ContinuousOn f₄ (orderedPositive n))
    (hi₁ : IntegrableOn f₁ (orderedPositive n)) (hi₂ : IntegrableOn f₂ (orderedPositive n))
    (hi₃ : IntegrableOn f₃ (orderedPositive n)) (hi₄ : IntegrableOn f₄ (orderedPositive n))
    (h₁ : ∀ x∈orderedPositive n,0≤f₁ x) (h₂ : ∀ x∈orderedPositive n,0≤f₂ x)
    (h₃ : ∀ x∈orderedPositive n,0≤f₃ x) (h₄ : ∀ x∈orderedPositive n,0≤f₄ x)
    (h : ∀ x∈orderedPositive n,∀ y∈orderedPositive n,
      f₁ x*f₂ y≤f₃ (x⊓y)*f₄ (x⊔y)) :
    (∫ x in orderedPositive n,f₁ x)*(∫ x in orderedPositive n,f₂ x) ≤
      (∫ x in orderedPositive n,f₃ x)*(∫ x in orderedPositive n,f₄ x) := by
  have hs (m : ℕ) : (orderedBox n (1/((m:ℝ)+1)) ((m:ℝ)+1) : Set (Fin n → ℝ))⊆orderedPositive n := by
    rw [orderedPositive_eq_iUnion]
    intro x hx
    exact mem_iUnion.mpr ⟨m,hx⟩
  have lim (f : (Fin n → ℝ) → ℝ) (hf : IntegrableOn f (orderedPositive n)) :
      Tendsto (fun m : ℕ ↦ ∫ x in (orderedBox n (1/((m:ℝ)+1)) ((m:ℝ)+1) : Set (Fin n → ℝ)),f x)
      atTop (nhds (∫ x in orderedPositive n,f x)) := by
    rw [orderedPositive_eq_iUnion] at hf ⊢
    exact tendsto_setIntegral_of_monotone (fun m ↦ (orderedBox_closed _ _ _).measurableSet)
      (orderedBox_exhaust_monotone n) hf
  apply le_of_tendsto_of_tendsto ((lim f₁ hi₁).mul (lim f₂ hi₂)) ((lim f₃ hi₃).mul (lim f₄ hi₄))
  apply Filter.Eventually.of_forall
  intro m
  exact orderedBox_continuousOn_four_functions n _ _ f₁ f₂ f₃ f₄
    (hc₁.mono (hs m)) (hc₂.mono (hs m)) (hc₃.mono (hs m)) (hc₄.mono (hs m))
    (fun x hx ↦ h₁ x (hs m hx)) (fun x hx ↦ h₂ x (hs m hx))
    (fun x hx ↦ h₃ x (hs m hx)) (fun x hx ↦ h₄ x (hs m hx))
    (fun x hx y hy ↦ h x (hs m hx) y (hs m hy))

end Honeycomb370

end

end OAI
