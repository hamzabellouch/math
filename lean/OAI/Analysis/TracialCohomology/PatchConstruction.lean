import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.CentralMatrices
import OAI.Analysis.TracialCohomology.WordQuantization
import OAI.Analysis.TracialCohomology.GoodExtensions

namespace OAI

/-! Patch construction for bounded Hochschild cohomology. -/

noncomputable section

namespace PopaPatching

theorem tolerance_schedule (L : ℕ) (δ E : ℝ) (hδ : 0<δ) (hE : 0<E) :
    ∃ ε : ℕ → ℝ, ∃ θ : ℝ, (∀ k, 0≤ε k) ∧ Monotone ε ∧ 0<θ ∧ ε L<E ∧
      ∀ k, 1≤k → k≤L → (2:ℝ)^L*(2*ε (k-1)/δ+(L:ℝ)*θ)≤ε k := by
  let N : ℝ := 2^L
  let R : ℝ := 2*N/δ+2
  let t : ℝ := E/(R^L+1)
  let ε : ℕ → ℝ := fun k => t*R^k
  let θ : ℝ := t/(N*((L:ℝ)+1))
  have hN : 0<N := pow_pos (by norm_num) _
  have hR : 1≤R := by
    have : 0≤2*N/δ := div_nonneg (by positivity) hδ.le
    dsimp [R]
    linarith
  have hRpos : 0<R := lt_of_lt_of_le (by norm_num) hR
  have ht : 0<t := div_pos hE (by positivity)
  have hθ : 0<θ := div_pos ht (mul_pos hN (by positivity))
  have heps (k) : 0≤ε k := mul_nonneg ht.le (pow_nonneg hRpos.le _)
  have hmono : Monotone ε := by
    apply monotone_nat_of_le_succ
    intro k
    dsimp [ε]
    rw [pow_succ]
    have hr := mul_le_mul_of_nonneg_left hR (pow_nonneg hRpos.le k)
    nlinarith
  have hL : ε L<E := by
    have he : t*(R^L+1)=E := div_mul_cancel₀ _ (by positivity)
    dsimp [ε]
    nlinarith
  refine ⟨ε,θ,heps,hmono,hθ,hL,fun k hk _ => ?_⟩
  have hk' : k=(k-1)+1 := by omega
  have heq : ε k=ε (k-1)*R := by
    change t*R^k=(t*R^(k-1))*R
    conv_lhs => rw [hk',pow_succ]
    ring
  have htε : t≤ε (k-1) := by
    have hh := hmono (show 0≤k-1 from Nat.zero_le _)
    simpa only [ε,pow_zero,mul_one] using hh
  have hθeq : θ*(N*((L:ℝ)+1))=t := div_mul_cancel₀ _ (by positivity)
  have hsmall : N*(L:ℝ)*θ≤ε (k-1) := by nlinarith
  rw [heq]
  dsimp [R]
  simp only [div_eq_mul_inv]
  nlinarith [heps (k-1)]
end PopaPatching

open scoped ComplexOrder
namespace PopaPatching
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma Rep.le_add (v w : Rep G M) (hvw : v.support*w.support=0) : v≤v.add w hvw := by
  have hwv : w.support*v.support=0 := by
    have hh := congrArg star hvw
    simpa only [star_mul,v.support_projection.isSelfAdjoint.star_eq,
      w.support_projection.isSelfAdjoint.star_eq,star_zero] using hh
  refine ⟨?_,fun g => ?_⟩
  · change v.support≤v.support+w.support
    exact le_add_of_nonneg_right w.support_projection.nonneg
  · change (v g+w g)*v.support=v g
    rw [add_mul,v.mul_support]
    have hh : w g*v.support=0 := by
      calc
        w g*v.support = (w g*w.support)*v.support := by rw [w.mul_support]
        _ = 0 := by rw [mul_assoc,hwv,mul_zero]
    rw [hh,add_zero]

lemma Rep.lt_add (v w : Rep G M) (hvw : v.support*w.support=0) (hw : w.support ≠ 0) :
    v<v.add w hvw := by
  refine lt_of_le_of_ne (v.le_add w hvw) ?_
  intro he
  have hh := congrArg Rep.support he.symm
  change v.support+w.support=v.support at hh
  exact hw (add_left_cancel (show v.support+w.support=v.support+0 by simpa using hh))

universe u v
variable {C B D : Type u} [Fintype C] [Fintype B]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in

theorem exists_good_extension (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (δ θ : ℝ) (hδ : 0<δ) (hθ : 0<θ)
    (hstep : ∀ k, 1≤k → k≤L → (2:ℝ)^L*(2*ε (k-1)/δ+(L:ℝ)*θ)≤ε k)
    (v : Rep (FreeGroup D) M) (hv : Good τ a γ L ε v)
    (hpδ : δ≤(τ (1-v.support)).re) :
    ∃ z : Rep (FreeGroup D) M, Good τ a γ L ε z ∧ v<z := by
  classical
  let p := 1-v.support
  have hp : IsStarProjection p := v.support_projection.one_sub
  have hp0 : p ≠ 0 := by
    intro hh
    have hz : (τ p).re=0 := by rw [hh,map_zero,Complex.zero_re]
    change δ≤(τ p).re at hpδ
    linarith
  obtain ⟨q,hq,hq0,hqp,hqt,he⟩ := quantize_words e τ hτ htr hfaith h1 hfactor hdiff hp hp0
    a γ v L θ (1/((2:ℝ)^L+1)) hθ (by positivity)
  let S : Finset (FreeGroup D) := (shortWords B L).image (fun bs => (bs.map γ).prod)
  obtain ⟨w,hw,hkill⟩ := finite_corner_rep e τ hτ htr hfaith h1 hfactor hdiff hq S
  have hvw : v.support*w.support=0 := by
    rw [hw]
    have hpeq : p*q=q := (hq.le_iff_mul_eq_right hp).mp hqp
    have hf : v.support*p=0 := by
      dsimp [p]
      rw [mul_sub,mul_one,v.support_projection.isIdempotentElem.eq,sub_self]
    calc
      v.support*q = v.support*(p*q) := by rw [hpeq]
      _ = 0 := by rw [←mul_assoc,hf,zero_mul]
  have hgood := good_add τ htr hfaith h1 a ha γ b0 hb0 L ε hε hmono v hv
    hp hp0 rfl hq hq0 w hw hvw δ θ hδ hpδ hθ.le
    (by simpa only [div_eq_mul_inv,one_mul,mul_comm] using hqt) hstep
    (fun bs hb hd => hkill _ (Finset.mem_image.mpr ⟨bs,(mem_shortWords bs L).mpr hb,rfl⟩) hd) he
  exact ⟨v.add w hvw,hgood,v.lt_add w hvw (by rwa [hw])⟩

include e hτ htr hfaith h1 hfactor in

theorem exists_almost_full_good (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (δ E : ℝ) (hδ : 0<δ) (hE : 0<E) :
    ∃ v : Rep (FreeGroup D) M,
      (τ (1-v.support)).re<δ ∧
      ∀ l : List (Letter C B), l.length≤L → degree γ l ≠ 1 → ‖τ (evaluate a γ v l)‖<E := by
  obtain ⟨ε,θ,hε,hmono,hθ,hεL,hstep⟩ := tolerance_schedule L δ E hδ hE
  obtain ⟨v,hv,hmax⟩ := maximal_good e τ hτ htr hfaith a ha γ L ε
  have hpδ : (τ (1-v.support)).re<δ := by
    by_contra hh
    obtain ⟨z,hz,hvz⟩ := exists_good_extension e τ hτ htr hfaith h1 hfactor hdiff
      a ha γ b0 hb0 L ε hε hmono δ θ hδ hθ hstep v hv (le_of_not_gt hh)
    exact hvz.not_ge (hmax z hz hvz.le)
  refine ⟨v,hpδ,fun l hl hd => ?_⟩
  exact (good_short_bound τ h1 a γ L ε hε hmono v hv l L hl hl hd).trans_lt hεL
end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching
universe u v
variable {C B D : Type u} [Fintype C] [Fintype B]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in

theorem exists_good_extension (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (δ θ : ℝ) (hδ : 0<δ) (hθ : 0<θ)
    (hstep : ∀ k, 1≤k → k≤L → (2:ℝ)^L*(2*ε (k-1)/δ+(L:ℝ)*θ)≤ε k)
    (v : Rep (FreeGroup D) M) (hv : Good e τ hτ htr hfaith a γ L ε v)
    (hpδ : δ≤(τ (1-v.support)).re) :
    ∃ z : Rep (FreeGroup D) M, Good e τ hτ htr hfaith a γ L ε z ∧ v<z := by
  classical
  let p := 1-v.support
  have hp : IsStarProjection p := v.support_projection.one_sub
  have hp0 : p ≠ 0 := by
    intro hh
    have hz : (τ p).re=0 := by rw [hh,map_zero,Complex.zero_re]
    change δ≤(τ p).re at hpδ
    linarith
  have hE1 : Homogeneous e τ hτ htr hfaith (1:M) := by
    change average e τ hτ htr hfaith 1=(τ 1).re • (1:M)
    rw [average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x),h1,Complex.one_re,one_smul]
  have hEp : Homogeneous e τ hτ htr hfaith p := homogeneous_sub e τ hτ htr hfaith h1 hE1 hv.1
  obtain ⟨q,hq,hq0,hqp,hqt,hEq,he⟩ := quantize_words e τ hτ htr hfaith h1 hII hp hp0 hEp
    a γ v L θ (1/((2:ℝ)^L+1)) hθ (by positivity)
  let S : Finset (FreeGroup D) := (shortWords B L).image (fun bs => (bs.map γ).prod)
  obtain ⟨w,hw,hkill⟩ := finite_corner_rep e τ hτ htr hfaith h1 hII hq hEq S
  have hvw : v.support*w.support=0 := by
    rw [hw]
    have hpeq : p*q=q := (hq.le_iff_mul_eq_right hp).mp hqp
    have hf : v.support*p=0 := by
      dsimp [p]
      rw [mul_sub,mul_one,v.support_projection.isIdempotentElem.eq,sub_self]
    calc
      v.support*q = v.support*(p*q) := by rw [hpeq]
      _ = 0 := by rw [←mul_assoc,hf,zero_mul]
  have hgood := good_add e τ hτ htr hfaith h1 hII a ha γ b0 hb0 L ε hε hmono v hv
    hp hp0 rfl hEp hq hq0 hEq w hw hvw δ θ hδ hpδ hθ.le
    (by simpa only [div_eq_mul_inv,one_mul,mul_comm] using hqt) hstep
    (fun bs hb hd => hkill _ (Finset.mem_image.mpr ⟨bs,(mem_shortWords bs L).mpr hb,rfl⟩) hd) he
  exact ⟨v.add w hvw,hgood,v.lt_add w hvw (by rwa [hw])⟩

include h1 in

theorem exists_almost_full_good (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (δ E : ℝ) (hδ : 0<δ) (hE : 0<E) :
    ∃ v : Rep (FreeGroup D) M,
      (τ (1-v.support)).re<δ ∧
      ∀ l : List (Letter C B), l.length≤L → degree γ l ≠ 1 → ‖τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l))‖<E := by
  obtain ⟨ε,θ,hε,hmono,hθ,hεL,hstep⟩ := tolerance_schedule L δ E hδ hE
  obtain ⟨v,hv,hmax⟩ := maximal_good e τ hτ htr hfaith h1 a ha γ L ε
  have hpδ : (τ (1-v.support)).re<δ := by
    by_contra hh
    obtain ⟨z,hz,hvz⟩ := exists_good_extension e τ hτ htr hfaith h1 hII
      a ha γ b0 hb0 L ε hε hmono δ θ hδ hθ hstep v hv (le_of_not_gt hh)
    exact hvz.not_ge (hmax z hz hvz.le)
  refine ⟨v,hpδ,fun l hl hd => ?_⟩
  exact (good_short_bound e τ hτ htr hfaith h1 a γ L ε hε hmono v hv l L hl hl hd).trans_lt hεL
end PopaCenter

end

end OAI
