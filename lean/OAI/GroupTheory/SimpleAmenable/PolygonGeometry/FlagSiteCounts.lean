import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagSites
import OAI.GroupTheory.SimpleAmenable.Arithmetic.QuadraticRectangleCounts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagSiteCounts
open Classical

theorem flagSite_key_injective {a m D : ℕ} {v : ℝ×ℝ} :
    Function.Injective (fun z : FlagSite a m D v => (z.val.1,flagSiteNumerator z)) := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p : Fin m × (CutRing×CutRing) => p.1) h
  · apply Subtype.ext
    rw [← flagSiteNumerator_spec z,← flagSiteNumerator_spec w]
    exact congrArg (scaledOrdinary D) (congrArg (fun p : Fin m × (CutRing×CutRing) => p.2) h)

noncomputable def flagSiteBox {a m D : ℕ} {v : ℝ×ℝ} (R : ℝ) : Set (FlagSite a m D v) :=
  {z | |(flagSiteConjugate z).1|≤R ∧ |(flagSiteConjugate z).2|≤R}

theorem flagSiteNumerator_box {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {R : ℝ} (z : FlagSite a m D v) (hz : z∈flagSiteBox R) :
    (flagSiteNumerator z).1∈cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) ∧
    (flagSiteNumerator z).2∈cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he₁ : ordinary (flagSiteNumerator z).1/(D:ℝ)=z.val.2.val.1 :=
    congrArg Prod.fst (flagSiteNumerator_spec z)
  have he₂ : ordinary (flagSiteNumerator z).2/(D:ℝ)=z.val.2.val.2 :=
    congrArg Prod.snd (flagSiteNumerator_spec z)
  have ho₁ := z.val.2.property.2.1
  have ho₂ := z.val.2.property.2.2.1
  have hc₁ := abs_le.mp hz.1
  have hc₂ := abs_le.mp hz.2
  change -R≤conjugate (flagSiteNumerator z).1/(D:ℝ) ∧
    conjugate (flagSiteNumerator z).1/(D:ℝ)≤R at hc₁
  change -R≤conjugate (flagSiteNumerator z).2/(D:ℝ) ∧
    conjugate (flagSiteNumerator z).2/(D:ℝ)≤R at hc₂
  rw [le_div_iff₀ hd,div_le_iff₀ hd] at hc₁ hc₂
  have he₁' := (div_eq_iff hd.ne').mp he₁
  have he₂' := (div_eq_iff hd.ne').mp he₂
  constructor <;> constructor <;> constructor <;>
    simp only [Set.mem_Icc] at * <;> nlinarith

theorem flagSiteBox_finite {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {R : ℝ} (hR : 0<R) : (flagSiteBox (a:=a) (m:=m) (D:=D) (v:=v) R).Finite := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have hf := cutRectangle_finite 0 (-(D:ℝ)*R) D (2*D*R) (by positivity)
  have hi : ((fun z : FlagSite a m D v => (z.val.1,flagSiteNumerator z)) '' flagSiteBox R).Finite := by
    refine ((Set.finite_univ : (Set.univ : Set (Fin m)).Finite).prod (hf.prod hf)).subset ?_
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨Set.mem_univ _,flagSiteNumerator_box hD z hz⟩
  exact hi.of_finite_image flagSite_key_injective.injOn

theorem flagSiteBox_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {R : ℝ} (hR : 0<R) (S : Finset (FlagSite a m D v))
    (hS : ∀z∈S,z∈flagSiteBox R) :
    (S.card:ℝ) ≤ m *(2*(D:ℝ)^2*R+2)^2 := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  let T := (cutRectangle_finite 0 (-(D:ℝ)*R) D (2*D*R) (by positivity)).toFinset
  have ht (u : CutRing) : u∈T ↔ u∈cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) :=
    Set.Finite.mem_toFinset _
  have hc : T.card < (2*(D:ℝ)^2*R+2) := by
    have hh := cutRectangle_card_bound T 0 (-(D:ℝ)*R) D (2*D*R) hd.le (by positivity)
      (fun u hu => (ht u).mp hu)
    nlinarith
  have hn : S.card ≤ m *T.card^2 := by
    rw [← Finset.card_image_of_injective _ flagSite_key_injective]
    have hi : S.image (fun z => (z.val.1,flagSiteNumerator z)) ⊆
        (Finset.univ : Finset (Fin m)) ×ˢ (T ×ˢ T) := by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      have hh := flagSiteNumerator_box hD z (hS z hz)
      simp only [Finset.mem_product,Finset.mem_univ,true_and]
      exact ⟨(ht _).mpr hh.1,(ht _).mpr hh.2⟩
    simpa [Finset.card_product,pow_two] using Finset.card_le_card hi
  have hn' : (S.card:ℝ) ≤ m *(T.card:ℝ)^2 := by exact_mod_cast hn
  have hh : (T.card:ℝ)^2≤(2*(D:ℝ)^2*R+2)^2 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) T.card]
  exact hn'.trans (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _))

end FlagSiteCounts

section FlagWindowCounts
open Classical

def flagWindow {a m D : ℕ} {v : ℝ×ℝ} (x y : ℝ×ℝ) (B C : ℝ) : Set (FlagSite a m D v) :=
  {z | z.val.2.val.1∈Set.Icc x.1 (x.1+B) ∧ z.val.2.val.2∈Set.Icc x.2 (x.2+B) ∧
    (flagSiteConjugate z).1∈Set.Icc y.1 (y.1+C) ∧
    (flagSiteConjugate z).2∈Set.Icc y.2 (y.2+C)}

theorem flagWindow_numerators {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    {x y : ℝ×ℝ} {B C : ℝ} (z : FlagSite a m D v) (hz : z∈flagWindow x y B C) :
    (flagSiteNumerator z).1∈cutRectangle (D*x.1) (D*y.1) (D*B) (D*C) ∧
    (flagSiteNumerator z).2∈cutRectangle (D*x.2) (D*y.2) (D*B) (D*C) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he₁ := congrArg Prod.fst (flagSiteNumerator_spec z)
  have he₂ := congrArg Prod.snd (flagSiteNumerator_spec z)
  change ordinary (flagSiteNumerator z).1/(D:ℝ)=z.val.2.val.1 at he₁
  change ordinary (flagSiteNumerator z).2/(D:ℝ)=z.val.2.val.2 at he₂
  have ho₁ := hz.1
  have ho₂ := hz.2.1
  rw [← he₁] at ho₁
  rw [← he₂] at ho₂
  have hc₁ : y.1≤conjugate (flagSiteNumerator z).1/(D:ℝ) ∧
      conjugate (flagSiteNumerator z).1/(D:ℝ)≤y.1+C := hz.2.2.1
  have hc₂ : y.2≤conjugate (flagSiteNumerator z).2/(D:ℝ) ∧
      conjugate (flagSiteNumerator z).2/(D:ℝ)≤y.2+C := hz.2.2.2
  simp only [Set.mem_Icc,le_div_iff₀ hd,div_le_iff₀ hd] at ho₁ ho₂ hc₁ hc₂
  constructor <;> constructor <;> constructor <;> nlinarith

theorem flagWindow_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (t : Fin m) {x y : ℝ×ℝ} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (S : Finset (FlagSite a m D v)) (hT : ∀z∈S,z.val.1=t)
    (hS : ∀z∈S,z∈flagWindow x y B C) :
    (S.card:ℝ) ≤ ((D:ℝ)^2*B*C+2)^2 := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  let T₁ := (cutRectangle_finite (D*x.1) (D*y.1) (D*B) (D*C) (mul_pos hd hC)).toFinset
  let T₂ := (cutRectangle_finite (D*x.2) (D*y.2) (D*B) (D*C) (mul_pos hd hC)).toFinset
  have hc₁ : (T₁.card:ℝ)<(D:ℝ)^2*B*C+2 := by
    have hh := cutRectangle_card_bound T₁ (D*x.1) (D*y.1) (D*B) (D*C)
      (mul_nonneg hd.le hB) (mul_pos hd hC) (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    nlinarith
  have hc₂ : (T₂.card:ℝ)<(D:ℝ)^2*B*C+2 := by
    have hh := cutRectangle_card_bound T₂ (D*x.2) (D*y.2) (D*B) (D*C)
      (mul_nonneg hd.le hB) (mul_pos hd hC) (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    nlinarith
  have hi : Set.InjOn (flagSiteNumerator (a:=a) (m:=m) (D:=D) (v:=v)) (↑S : Set (FlagSite a m D v)) := by
    intro z hz w hw hn
    apply flagSite_key_injective
    exact Prod.ext ((hT z hz).trans (hT w hw).symm) hn
  have hn : S.card ≤ T₁.card*T₂.card := by
    rw [← Finset.card_image_of_injOn hi,← Finset.card_product]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
    have hh := flagWindow_numerators hD z (hS z hz)
    simpa only [Finset.mem_product,T₁,T₂,Set.Finite.mem_toFinset] using hh
  have hn' : (S.card:ℝ) ≤ (T₁.card:ℝ)*(T₂.card:ℝ) := by exact_mod_cast hn
  calc
    (S.card:ℝ) ≤ (T₁.card:ℝ)*(T₂.card:ℝ) := hn'
    _ ≤ ((D:ℝ)^2*B*C+2)*((D:ℝ)^2*B*C+2) :=
      mul_le_mul hc₁.le hc₂.le (Nat.cast_nonneg _) (by positivity)
    _ = _ := (pow_two _).symm

end FlagWindowCounts

end SimpleAmenable
end
end

end OAI
