import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.HeavyPlaneInput
import OAI.Combinatorics.SharpRamsey.Planar.PlanarComplete

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset Real Filter SourceScales Incidence PreparedProjectiveGeometry
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedHeavyPlaneCover_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedHeavyPlaneCover_2 : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedHeavyPlaneCover_3 (W : Submodule K V) : Fintype (Projectivization K W) := by
  let : Finite W := Module.finite_of_finite K
  exact Fintype.ofFinite _

lemma planeSupport_mono (W : Submodule K V) {S U : Finset (Projectivization K V)}
    (h : S⊆U) : planeSupport W S⊆planeSupport W U := by
  intro a ha
  exact mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp ha).2⟩

lemma plane_cap_lift (W : Submodule K V) (U S : Finset (Projectivization K V))
    (E : Finset (Projectivization K W)) (hE : E⊆planeSupport W U) :
    E.image (Projectivization.map W.subtype W.injective_subtype)⊆U ∧
    (E.image (Projectivization.map W.subtype W.injective_subtype)).card=E.card ∧
    (S∩E.image (Projectivization.map W.subtype W.injective_subtype)).card=
      (planeSupport W S∩E).card := by
  have hi := Projectivization.map_injective W.subtype W.injective_subtype
  refine ⟨?_,card_image_of_injective _ hi,?_⟩
  · intro a ha
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    exact (mem_filter.mp (hE hx)).2
  · have he : (planeSupport W S∩E).image (Projectivization.map W.subtype W.injective_subtype)=
        S∩E.image (Projectivization.map W.subtype W.injective_subtype) := by
      ext a
      constructor
      · intro ha
        obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
        exact mem_inter.mpr ⟨(mem_filter.mp (mem_inter.mp hx).1).2,
          mem_image.mpr ⟨x,(mem_inter.mp hx).2,rfl⟩⟩
      · intro ha
        obtain ⟨ha,hE⟩ := mem_inter.mp ha
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hE
        exact mem_image.mpr ⟨x,mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ha⟩,hx⟩,rfl⟩
    rw [←he,card_image_of_injective _ hi]

lemma heavy_domain_gaps (N M N₁ M₁ n t a u h L : ℝ)
    (hN : 0<N) (hM : 0<M) (hn : 0<n) (ht : 0<t)
    (ha : 0<a) (hu : 0<u) (_hh : 0<h) (hL : 0<L)
    (hN₁ : 0<N₁) (hM₁ : 0<M₁) (hcap : N₁≤N) (hheavy : n≤50*a)
    (hdom : h*M₁≤M) (hsize : t≤4*h*L*u) :
    log (N₁/a)≤log (N/n)+log 50 ∧
    log (M₁/u)≤log (M/t)+log (4*L) := by
  constructor
  · rw [←log_mul (div_pos hN hn).ne' (by norm_num : (50:ℝ)≠0)]
    apply log_le_log (div_pos hN₁ ha)
    apply (div_le_iff₀ ha).mpr
    have hratio : N≤N/n*(50*a) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hn).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hheavy hN.le]
    nlinarith
  · rw [←log_mul (div_pos hM ht).ne' (mul_pos (by norm_num) hL).ne']
    apply log_le_log (div_pos hM₁ hu)
    apply (div_le_iff₀ hu).mpr
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (le_div_iff₀ ht).mpr
    have hm := mul_le_mul_of_nonneg_left hsize hM₁.le
    have hd := mul_le_mul_of_nonneg_right hdom (by positivity : 0≤4*L*u)
    nlinarith

theorem fixed_heavy_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ D R,Admissible σ η D R → exp σ=(Nat.card K:ℝ) →
    ∀ (W : Submodule K V),Module.finrank K W=3 →
    ∀ (U : Finset (Projectivization K V))
      (U₁ : Finset (Projectivization K (Module.Dual K W))) (n a t : ℕ) (b τ : ℝ),
    0<a → 0<t → a≤n → n≤50*a → a≤(planeSupport W U).card → t≤U₁.card →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    (Nat.card K:ℝ)^3*exp (-b)≤(a:ℝ)*t → (a:ℝ)*t≤2*(Nat.card K:ℝ)^3 →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ E∈caps,E⊆U ∧ (E.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → (planeSupport W S).card=a → T⊆U₁ → T.card=t →
        (incidenceCount (planeSupport W S) T:ℝ)≤τ*(a:ℝ)*t/Nat.card K →
        ∃ E∈caps,(n:ℝ)/100≤(S∩E).card) ∧
      log ((caps.card:ℝ)+1)≤2000*(Nat.card K:ℝ)*P*
        (log (((planeSupport W U).card:ℝ)/a)+log ((U₁.card:ℝ)/t)+P) := by
  filter_upwards [PlanarLearning.complete_cover hη C hC] with σ hcover
  intro K V _ _ _ _ _ D R had hex W hW U U₁ n a t b τ ha ht han hna hau htu hb hbu hτ hτu hlo hhi
  obtain ⟨caps,hs,hc,hl⟩ := hcover K W D R had hex hW (planeSupport W U) U₁ a t b τ
    ha ht hau htu hb hbu hτ hτu hlo hhi
  let f := fun E : Finset (Projectivization K W) =>
    E.image (Projectivization.map W.subtype W.injective_subtype)
  refine ⟨caps.image f,?_,?_,?_⟩
  · intro E hE
    obtain ⟨E₀,hE₀,rfl⟩ := mem_image.mp hE
    obtain ⟨hEU,hsize⟩ := hs E₀ hE₀
    obtain ⟨hsub,hcard,_⟩ := plane_cap_lift W U ∅ E₀ hEU
    refine ⟨hsub,?_⟩
    dsimp only [f]
    rw [hcard]
    exact hsize.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast han) (exp_pos _).le)
  · intro S T hSU _ hSa hTU hTt hsp
    obtain ⟨E,hE,hcap⟩ := hc (planeSupport W S) T (planeSupport_mono W hSU) hSa hTU hTt hsp
    refine ⟨f E,mem_image.mpr ⟨E,hE,rfl⟩,?_⟩
    obtain ⟨_,_,he⟩ := plane_cap_lift W U S E (hs E hE).1
    dsimp only [f]
    rw [he]
    have hna' : (n:ℝ)≤50*a := by exact_mod_cast hna
    linarith
  · apply le_trans _ hl
    apply log_le_log (by positivity)
    have hh := card_image_le (s:=caps) (f:=f)
    exact_mod_cast Nat.add_le_add_right hh 1

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
