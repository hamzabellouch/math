import OAI.Probability.BenjaminiSchramm.TruncatedSlabMoment

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def heightMaximumSlice (D : Set E) (f : V → ℝ) (s : ℝ) (n : ℕ) (x : V) : Set (Set E) :=
  (restrictedHit G D x {z | s*((n : ℝ)+1) ≤ f z})ᶜ ∩
    restrictedHit G D x {z | s*n ≤ f z}

lemma finite_cluster_height_slices_cover (D : Set E) (f : V → ℝ) (s : ℝ) (hs : 0 < s)
    (ω : Set E) (x : V) (hx : f x=0) (hfin : (cluster G (ω ∩ D) x).Finite) :
    ∃ n, ω ∈ heightMaximumSlice G D f s n x := by
  obtain ⟨b,hb⟩ := (hfin.image f).bddAbove
  obtain ⟨N,hN⟩ := exists_nat_gt (b/s)
  have hno : ∃ n : ℕ, ω ∉ restrictedHit G D x {z | s*((n : ℝ)+1) ≤ f z} := by
    refine ⟨N,?_⟩
    rintro ⟨z,hz,hxz⟩
    have hh : f z ≤ b := hb ⟨z,hxz,rfl⟩
    have hn : b < s*N := by
      have hn' := (div_lt_iff₀ hs).mp hN
      nlinarith
    change s*((N : ℝ)+1) ≤ f z at hz
    nlinarith
  let n := Nat.find hno
  refine ⟨n,Nat.find_spec hno,?_⟩
  by_cases hn : n=0
  · refine ⟨x,?_,conn_refl G _ x⟩
    simp only [hn,Nat.cast_zero,mul_zero,Set.mem_ofPred_eq,hx,le_refl]
  · have hmin := Nat.find_min hno (show n-1 < Nat.find hno by dsimp [n]; omega)
    have he : ((n-1 : ℕ) : ℝ)+1=(n : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one]
      ring
    simpa only [he,not_not] using hmin

variable [Countable V] [Countable E]

lemma measurableSet_heightMaximumSlice (D : Set E) (f : V → ℝ) (s : ℝ) (n : ℕ) (x : V) :
    MeasurableSet (heightMaximumSlice G D f s n x) :=
  (measurableSet_restrictedHit G D x _).compl.inter (measurableSet_restrictedHit G D x _)

omit [Countable V] [Countable E] in
lemma ae_height_slices_cover (p : unitInterval) (D : Set E) (f : V → ℝ) (s : ℝ) (hs : 0 < s)
    (x : V) (hx : f x=0) (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    ∀ᵐ ω ∂law p, ∃ n, ω ∈ heightMaximumSlice G D f s n x := by
  filter_upwards [hfin] with ω hω
  exact finite_cluster_height_slices_cover G D f s hs ω x hx
    (hω.subset fun z hz => conn_mono G Set.inter_subset_left hz)

end Percolation.BenjaminiSchramm

end

end OAI
