import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryModulusBounded
import OAI.Geometry.Cannon.Energy.ApproxSelfSimilar
import OAI.Geometry.Cannon.Uniformization.LayerFamily

namespace OAI

section
section
section
namespace CannonCells
open Set CannonDuality

noncomputable section
variable {X ι : Type*} [Fintype ι]

lemma modulus_family_mono (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {F H : Set (Set X)} (hFH : F ⊆ H) (hH : ∀ A ∈ H, A.Nonempty) :
    modulus C F ≤ modulus C H := by
  classical
  let w : Weights ι := WithLp.toLp 2 (fun _ => (1:ℝ))
  have hw : Admissible (familyVectors C H : Set (Weights ι)) w := by
    rw [admissible_iff]
    refine ⟨fun _ => zero_le_one,?_⟩
    intro A hA
    obtain ⟨x,hx⟩ := hH A hA
    obtain ⟨i,hi⟩ := hC x
    have hm : i ∈ indices C A := (mem_indices C A i).mpr ⟨x,hx,hi⟩
    exact Finset.single_le_sum (fun _ _ => zero_le_one) hm
  unfold modulus Modulus
  apply csInf_le_csInf
  · refine ⟨0,?_⟩
    rintro e ⟨z,_,rfl⟩
    exact sq_nonneg _
  · exact ⟨‖w‖^2,w,hw,rfl⟩
  · rintro e ⟨z,hz,rfl⟩
    refine ⟨z,?_,rfl⟩
    rw [admissible_iff] at hz ⊢
    exact ⟨hz.1,fun A hA => hz.2 A (hFH hA)⟩
end
end CannonCells

namespace CannonUniformization
open Set Metric Filter Topology unitInterval CannonDuality CannonCells CannonCharts

noncomputable section
variable {X : Type*} [MetricSpace X] [PathConnectedSpace X]

theorem annular_modulus_smallness (Q : ℕ) (CP L a : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q CP) (hCP : 0 ≤ CP)
    (hL : 1 ≤ L) (ha : 1 < a) (hdiam1 : diam (univ : Set X) ≤ 1)
    (hsim : ∀ o : X, ∀ s : ℝ, 0 < s → s ≤ diam (univ : Set X) →
      ∃ f : X ≃ₜ X, ∀ x ∈ ball o s, ∀ y ∈ ball o s,
        dist (f x) (f y)*s ≤ L*dist x y ∧ dist x y ≤ L*dist (f x) (f y)*s)
    (ι : ℕ → Type*) [∀ m, Fintype (ι m)] (p : ∀ m, ι m → X)
    (hpsep : ∀ m i j, i ≠ j → (a^m)⁻¹ ≤ dist (p m i) (p m j))
    (hpnet : ∀ m x, ∃ i, dist (p m i) x ≤ (a^m)⁻¹)
    (d B : ℝ) (hd : 0 < d) (hdiam : d < diam (univ : Set X)) (hdL : d ≤ 1/(4*L))
    (hB : ∀ m, modulus (fun i => ball (p m i) (2*(a^m)⁻¹)) (macroFamily d) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ ratio : ℝ, 1 < ratio ∧ ∀ R : ℝ,
      0 < R → R ≤ diam (univ : Set X) → ∀ᶠ m : ℕ in atTop, ∀ o : X,
        modulus (fun i => ball (p m i) (2*(a^m)⁻¹)) (annulusFamily o (R/ratio) R) < ε := by
  classical
  obtain ⟨E,hE,hdecay⟩ := annular_modulus_decay Q CP L a hpack hCP hL ha hsim
    ι p hpsep hpnet d B hd hdiam hdL hB
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_gt (E*B/ε)
  have hnε : E*B/(n+1:ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < n+1)]
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith
  obtain ⟨ℓ,hℓ⟩ := pow_unbounded_of_one_lt (8:ℝ) ha
  let ratio := 8*a*a^(ℓ*n)
  have hap : 0 < a := zero_lt_one.trans ha
  have hpow : 1 ≤ a^(ℓ*n) := one_le_pow₀ ha.le
  have hratio : 1 < ratio := by dsimp [ratio]; nlinarith
  refine ⟨ratio,hratio,?_⟩
  intro R hR hRdia
  obtain ⟨k₀,hklo,hkhi⟩ := CannonNet.exists_scale_below ha
    (show 0 < R/4 by positivity) (show R/4 ≤ 1 by linarith [hRdia.trans hdiam1])
  have hk₀ : 4*(a^k₀)⁻¹ ≤ diam (univ : Set X) := by linarith
  have hr : R/ratio ≤ (a^(k₀+ℓ*n))⁻¹ := by
    rw [pow_add,mul_inv]
    have h₁ : R/(8*a) ≤ (a^k₀)⁻¹ := by
      have hid : R/4/a=R/(4*a) := by ring
      rw [hid] at hklo
      have hh : R/(8*a) ≤ R/(4*a) := div_le_div_of_nonneg_left hR.le (by positivity) (by nlinarith)
      exact hh.trans hklo.le
    have hh := mul_le_mul_of_nonneg_right h₁ (inv_nonneg.mpr (pow_nonneg hap.le (ℓ*n)))
    calc
      R/ratio = (R/(8*a))*(a^(ℓ*n))⁻¹ := by dsimp [ratio]; ring
      _ ≤ (a^k₀)⁻¹*(a^(ℓ*n))⁻¹ := hh
  have ht := hdecay ℓ k₀ n hℓ.le hk₀
  filter_upwards [ht] with m hm
  intro o
  have hmono : modulus (fun i => ball (p m i) (2*(a^m)⁻¹)) (annulusFamily o (R/ratio) R) ≤
      modulus (fun i => ball (p m i) (2*(a^m)⁻¹))
        (annulusFamily o (a^(k₀+ℓ*n))⁻¹ (2*(a^k₀)⁻¹)) := by
    apply modulus_family_mono _ ?_ ?_ ?_
    · intro x
      obtain ⟨i,hi⟩ := hpnet m x
      refine ⟨i,?_⟩
      change dist x (p m i) < _
      rw [dist_comm]
      have hh : 0 < (a^m)⁻¹ := inv_pos.mpr (pow_pos hap _)
      linarith
    · rintro A ⟨u,v,p,rfl,hu,hv⟩
      exact ⟨u,v,p,rfl,hu.trans hr,(show 2*(a^k₀)⁻¹ ≤ R by linarith).trans hv⟩
    · rintro A ⟨u,v,p,rfl,_,_⟩
      exact range_nonempty p
  exact (hmono.trans (hm o)).trans_lt hnε

end
end CannonUniformization

end
namespace CannonRelease
open CannonGraph CannonVisual CannonGeometry CannonNet CannonCells CannonCharts
open Set Metric Filter Topology

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_annular_modulus_smallness (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    ∃ T : ℕ → Finset (Boundary D),
      (∀ n, (∀ x ∈ T n, ∀ y ∈ T n, x ≠ y → (a^n)⁻¹ ≤ dist x y) ∧
        (∀ x, ∃ y ∈ T n, dist y x ≤ (a^n)⁻¹)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ratio : ℝ, 1 < ratio ∧ ∀ R : ℝ,
        0 < R → R ≤ diam (univ : Set (Boundary D)) →
        ∀ᶠ m : ℕ in atTop, ∀ o : Boundary D,
          modulus (fun i : T m => ball i.val (2*(a^m)⁻¹))
            (CannonUniformization.annulusFamily o (R/ratio) R) < ε := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : PathConnectedSpace SphereTwo := CannonCharts.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) :=
    φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  dsimp only
  let a := Real.exp (2*visualExponent δ)
  let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  have hLE : 0 < LE := by dsimp [LE]; positivity
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  obtain ⟨T,hT⟩ := exists_net_sequence (X:=Boundary D) ha
  obtain ⟨L,hL,hsim⟩ := boundary_approx_self_similar D hδ
  obtain ⟨Q,CP,hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  have hdia1 : diam (univ : Set (Boundary D)) ≤ 1 :=
    diam_le_of_forall_dist_le zero_le_one (fun x _ y _ => boundaryDist_le_one D hδ x y)
  have hdia : 0 < diam (univ : Set (Boundary D)) := by
    apply diam_pos ?_ (isCompact_univ.isBounded)
    let v : SphereTwo := ⟨EuclideanSpace.single 0 1,by simp⟩
    let w : SphereTwo := ⟨EuclideanSpace.single 0 (-1),by simp⟩
    refine ⟨φ.symm v,mem_univ _,φ.symm w,mem_univ _,?_⟩
    intro hh
    have he := congrArg (fun z : SphereTwo => z.val 0) (φ.symm.injective hh)
    norm_num [v,w] at he
  let d := min (diam (univ : Set (Boundary D))/2) (min (1/(LE*3^2)) (1/(4*L)))
  have hd : 0 < d := by dsimp [d]; exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hddia : d < diam (univ : Set (Boundary D)) :=
    (min_le_left _ _).trans_lt (by linarith)
  have hdLE : d ≤ 1/(LE*3^2) := (min_le_right _ _).trans (min_le_left _ _)
  have hdL : d ≤ 1/(4*L) := (min_le_right _ _).trans (min_le_right _ _)
  have hsep (n : ℕ) (i j : T n) (hij : i ≠ j) : (a^n)⁻¹ ≤ dist i.val j.val :=
    (hT n).1 i.val i.property j.val j.property (fun hh => hij (Subtype.ext hh))
  have hnet (n : ℕ) (x : Boundary D) : ∃ i : T n, dist i.val x ≤ (a^n)⁻¹ := by
    obtain ⟨y,hy,hh⟩ := (hT n).2 x
    exact ⟨⟨y,hy⟩,hh⟩
  obtain ⟨B,hB⟩ := boundary_modulus_bounded D hδ φ d hd hddia hdLE
    (fun n => ↥(T n)) (fun n i => i.val) hsep hnet
  exact ⟨T,hT,CannonUniformization.annular_modulus_smallness Q CP L a hpack hCP.le hL ha
    hdia1 hsim (fun n => ↥(T n)) (fun n i => i.val) hsep hnet d B hd hddia hdL hB⟩

end CannonRelease

end
end

end OAI
