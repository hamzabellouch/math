import OAI.Combinatorics.HadwigerCounterexample.RelativeEntropy

namespace OAI

/-! # Projection Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

theorem map_mass (p : Wgt A) (f : A→B) : tot (mapW p f)=tot p := by
  simpa only [avg_const,mul_one] using mapW_avg p f (fun _ => 1)
omit [Fintype B] in
theorem map_nz {p : Wgt A} (hp : ∀ i, 0 ≤ p i) (f : A→B) (i : B) :
    0 ≤ mapW p f i := pr_nonneg hp
omit [Fintype B] in
theorem lsupp_witness {p : Wgt A} {f : A→B} {i}
    (h : mapW p f i≠0) : ∃ x,p x≠0 ∧ f x=i := by
  classical
  by_contra! hh
  refine h (Finset.sum_eq_zero (fun x _ => ?_))
  by_cases h : p x=0
  · change p x * ind _=0
    rw [h,zero_mul]
  exact (congrArg (p x * ·) (ind_zero (hh x h))).trans (mul_zero _)

omit [Fintype B] in
theorem lsupp_hit {p : Wgt A} (hp : ∀ i,0 ≤ p i) (f : A→B) (x : A) (h : p x≠0) :
    mapW p f (f x)≠0 := by
  have h' := lt_of_le_of_ne (hp x) (Ne.symm h)
  have he := weight_le_tot (fun y => mul_nonneg (hp y) (ind_nonneg (f y = f x))) x
  simp only [ind_true,mul_one] at he
  exact (h'.trans_le he).ne'

omit [Fintype B] in
theorem lsupp.map {p q : Wgt A} (h : lsupp p q) (hq : ∀ i,0 ≤ q i)
    (f : A→B) : lsupp (mapW p f) (mapW q f) := by
  intro i hi
  obtain ⟨x,hx,rfl⟩ := lsupp_witness hi
  exact lsupp_hit hq f x (h x hx)

omit [Fintype C] in
theorem map_nested {p : Wgt A} (f : A→B) (g : B→C) :
    mapW (mapW p f) g = mapW p (g ∘ f) := funext fun _ => mapW_pr p f _

omit [Fintype C] in
theorem map_mix (w : Wgt A) (p : A→ Wgt B) (f : B→C) :
    mapW (mixW w p) f = mixW w (fun i => mapW (p i) f) := funext fun _ => mixW_avg ..

omit [Fintype B] in
theorem map_resize (p : Wgt A) (f : A→B) (u : Wgt B) :
    mapW (fun i => p i*u (f i)) f = (fun i => mapW p f i * u i) := by
  funext i
  unfold mapW pr avg
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  by_cases h : f j=i
  · simp only [h,ind_true,mul_one]
  simp only [ind_zero h,mul_zero,zero_mul]

def pour (q : Wgt A) (f : A→B) (w : Wgt B) :=
  fun i => q i * (w (f i) / mapW q f (f i))

omit [Fintype B] in
theorem map_pour (q : Wgt A) (f : A → B) (w : Wgt B) (h : lsupp w (mapW q f)) :
    mapW (pour q f w) f=w := by
  unfold pour
  rw [map_resize (u:=fun i => w i / mapW q f i)]
  funext i
  by_cases he : w i=0
  · simp only [he,zero_div,mul_zero]
  have hm := h i he
  field_simp

def bucket (q : Wgt A) (f : A→B) (p : Wgt A) := pour q f (mapW p f)

omit [Fintype B] in
theorem pour_nz {q : Wgt A} {u : Wgt B} (f : A→B)
    (hq : ∀ i,0 ≤ q i) (hu : ∀ i,0 ≤ u i) (i) : 0 ≤ pour q f u i :=
  mul_nonneg (hq i) (div_nonneg (hu _) (map_nz hq f _))

omit [Fintype B] in
theorem bucket_scale (q p : Wgt A) (hq : ∀ i,0≤q i) (h : lsupp p q) (f : A→B) :
    mapW (bucket q f p) f=mapW p f := map_pour q f _ (lsupp.map h hq f)

theorem bucket_law {q p : Wgt A} (hp : IsLaw p)
    (f : A→B) (hq : ∀ i,0≤q i) (h : lsupp p q) :
    IsLaw (bucket q f p) := by
  refine ⟨pour_nz f hq (map_nz hp.nz f),?_⟩
  rw [←map_mass _ f,bucket_scale q p hq h,map_mass,hp.total]

omit [Fintype B] in
theorem lsupp_bucket {p q : Wgt A} (f : A → B) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i,0 ≤ q i) (h : lsupp p q) : lsupp p (bucket q f p) :=
  fun x hx => mul_ne_zero (h x hx) (div_ne_zero (lsupp_hit hp f x hx) (lsupp_hit hq f x (h x hx)))

omit [Fintype C] in
theorem bucket_nested (q p : Wgt A) (f : A→B) (g : B→C) :
    mapW (bucket q (g ∘ f) p) f=bucket (mapW q f) g (mapW p f) := by
  unfold bucket pour
  rw [map_nested,map_nested]
  have h := map_resize q f (fun i=>mapW p (g∘f) (g i)/mapW q (g∘f) (g i))
  exact h

omit [Fintype B] in
theorem bucket_mix (q : Wgt A) (f : A → B) (w : Wgt C) (p : C→ Wgt A) :
    bucket q f (mixW w p)=mixW w (fun y => bucket q f (p y)) := by
  unfold bucket pour
  rw [map_mix]
  funext i; simp only [mixW,avg_mul',avg_div]

theorem tension_stage (p q : Wgt A) (hp : ∀ i,0 ≤ p i) (hq : ∀ i, 0≤ q i)
    (h : lsupp p q) (f : A→B) :
    tension p q=tension p (bucket q f p)+tension (mapW p f) (mapW q f) := by
  unfold tension
  rw [mapW_avg, ← avg_add]
  refine avg_congr (fun i hi => ?_)
  have hu := h i hi; have hw := lsupp_hit hp f i hi; have hv := lsupp_hit hq f i hu
  dsimp only [bucket,pour]
  rw [log_mul hu (div_ne_zero hw hv),log_div hw hv]
  ring
end HadwigerCounterexample

end

end OAI
