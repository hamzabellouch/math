import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.RestrictionScale
import OAI.Combinatorics.RamseyFive.Geometry.DimensionTwoOriented
import OAI.Combinatorics.RamseyFive.Geometry.FlatSection

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma map_option_none (p : Law (Option α)) (f : α→β) : map p (Option.map f) none=p none := by
  simp only [map,Fintype.sum_option,Option.map_none,ite_true,Option.map_some,
    Option.some_ne_none,ite_false,Finset.sum_const_zero,add_zero]
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_plane_reduction_law {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)],
    ∀ (A : Submodule K V)
      [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
      [Fintype (ℙ K (Dual K (Dual K A)))]
      [∀x : ℙ K A,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K A),Fintype (RadialLine x)],
    ∀ (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K A=3 → finrank K V≤5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      let S := flatSection A X
      let US := flatSection A UX
      let M := (Nat.card K)^(finrank K V-finrank K A)
      let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
      ∃k, k≤Nat.log 2 M ∧
      ∃hT₀ : (restrictions (image A.dualRestrict) G k).Nonempty,
        let T₀ := restrictions (image A.dualRestrict) G k
        let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
        let pp := twoOrientedLaw S US T₀ UT₀ hT₀ (P η σ D R) (Real.sqrt τ) R L₀
        let p := map pp (Option.map fun Z=>Z.map (flatEmbedding A))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (2*P η σ D R) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)<(1:ℝ)/200 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<1/200)
  filter_upwards [eventually_two_oriented hη hη' (Cb+1) (by linarith),
    eventually_restriction_overheads hη hη',ht,eventually_ge_atTop (1:ℝ)] with σ hbase hover ht hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ A _ _ _ _ _ X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  have htroot : Real.sqrt τ≤σ^(-200*beta η) := by
    have hh := root_density_scale (j:=2) (d:=3) hσ hτ.le (beta_pos hη).le (by norm_num) (by norm_num)
      (show τ≤σ^(-200*(2:ℝ)^(3-2)*beta η) by norm_num;simpa only [neg_mul] using hτhi)
    simpa using hh
  have hsmall : Real.sqrt τ≤1/200 := htroot.trans ht.le
  obtain ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ :=
    original_large_cell A X UX T UT hX hT hXU hTU τ b hτ hsmall hflat hprod hdens
  dsimp only
  refine ⟨k,hk,hT₀,?_⟩
  let S := flatSection A X
  let US := flatSection A UX
  let M := (Nat.card K)^(finrank K V-finrank K A)
  let B := b+Real.log (400*(Nat.log 2 M+1:ℝ))
  let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
  let T₀ := restrictions (image A.dualRestrict) G k
  let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
  let pp := twoOrientedLaw S US T₀ UT₀ hT₀ (P η σ D R) (Real.sqrt τ) R L₀
  have hB : 0≤B := by
    refine add_nonneg hb (Real.log_nonneg ?_)
    have hn : (0:ℝ)≤Nat.log 2 M := by positivity
    linarith only [hn]
  have hBhi : B≤(Cb+1)*D*σ^(6*beta η) :=
    (hover D R b Cb (Nat.card K) (finrank K V-finrank K A) hr hq (by omega) hbhi).2.2
  have hp' : (Nat.card K:ℝ)^3*Real.exp (-B)≤(S.card:ℝ)*T₀.card := by
    simpa only [S,T₀,G,B,M,hA,Nat.cast_add,Nat.cast_one] using hp
  obtain ⟨hfail,hgood⟩ := hbase D B (Real.sqrt τ) R L₀ K A S US T₀ UT₀ hT₀ hA hq hr hL
    hB hBhi (Real.sqrt_pos.mpr hτ) htroot hS hSU hTU₀ hd hp'
  change map pp (Option.map fun Z=>Z.map (flatEmbedding A)) none≤_ ∧ _
  refine ⟨by rw [map_option_none];exact hfail,?_⟩
  intro W hW
  obtain ⟨Z,hZ,he⟩ := map_positive pp (Option.map fun Z=>Z.map (flatEmbedding A)) (some W) hW
  cases Z with
  | none => simp at he
  | some Z =>
    have he' : Z.map (flatEmbedding A)=W := Option.some.inj he
    subst W
    have hz := hgood Z hZ
    obtain ⟨hu,hcard,hcap⟩ := section_decoder A X UX Z hz.1
    refine ⟨hu,?_,?_⟩
    · rw [hcard]
      exact hz.2.1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsX) (Real.exp_pos _).le)
    · rw [hcap,Finset.inter_comm]
      have hc := hz.2.2
      nlinarith only [hc,hxs]

end SharpRamseyFive.ProjectiveRestriction

end OAI
