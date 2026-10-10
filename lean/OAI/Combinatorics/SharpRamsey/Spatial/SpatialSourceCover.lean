import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialActualCover
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialParameters

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SourceScales SpatialLearning DescriptionHeaders PreparedProjectiveGeometry
open scoped Classical BigOperators Topology NNReal
noncomputable section
local instance flat_JoinedSpatialSourceCover_1 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Fin 4 → ZMod q)) :=
  Fintype.ofFinite _
local instance flat_JoinedSpatialSourceCover_2 (q : ℕ) [Fact q.Prime] :
    Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) := by
  letI : Finite (Module.Dual (ZMod q) (Fin 4 → ZMod q)) := Module.finite_of_finite (ZMod q)
  exact Fintype.ofFinite _
local instance flat_JoinedSpatialSourceCover_3 (q : ℕ) [Fact q.Prime] : Finite (Submodule (ZMod q) (Fin 4 → ZMod q)) :=
  Finite.of_injective (fun W : Submodule (ZMod q) (Fin 4 → ZMod q) => (W : Set (Fin 4 → ZMod q)))
    SetLike.coe_injective

theorem source_cover {η : ℝ} (hη : 0 < η) (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ = (q:ℝ) →
    ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))) (n : ℕ) (b τ : ℝ),
    0 < n → n ≤ U.card → (n:ℝ) ≤ 2*(q:ℝ)^2 → 200*(q:ℝ)*scaleP σ η D R ≤ n →
    0 ≤ b → b ≤ C*scaleKstar σ η D → 0 < τ → τ ≤ C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    let J := ⌈exp (7*σ/10)⌉₊
    let M := ⌈2*(q:ℝ)*P⌉₊
    let H := (Fintype.card (Projectivization (ZMod q) (Fin 4 → ZMod q)):ℝ)*log 2
    let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
      log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))):ℝ)+1)
    ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))),
      (∀ W ∈ caps, W ⊆ U ∧ (W.card:ℝ) ≤ n*exp (6*P)) ∧
      (∀ (S : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q)))
          (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q)))),
        S ⊆ U → S.card = n → T.Nonempty → S.card ≤ T.card →
        (q:ℝ)^4*exp (-b) ≤ (S.card:ℝ)*T.card →
        (Incidence.incidenceCount S T:ℝ) ≤ τ*(S.card:ℝ)*T.card/q →
        (∃ W : Submodule (ZMod q) (Fin 4 → ZMod q), Module.finrank (ZMod q) W = 3 ∧
          (n:ℝ)/50 ≤ (S ∩ planePoints W).card) ∨
        (∃ W ∈ caps, (n:ℝ)/4 ≤ (S ∩ W).card)) ∧
      (caps.card:ℝ) ≤ (n+1:ℕ)*(J+1:ℕ)*
        (((Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q))*(n+1)+1:ℕ):ℝ)^J)*exp E := by
  have hβ := beta_pos hη
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 100*beta η)).const_mul C
  have hK : ∀ᶠ σ : ℝ in atTop, (1:ℝ) ≤ σ^(7*beta η) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with σ hσ
    exact one_le_rpow hσ (by positivity)
  filter_upwards [actual_cover (beta η) (log 2) hβ,
    eventually_bounded_budget hη,eventually_grid_shape 2,
    eventually_P_le_linear hη (1/40) (by norm_num),
    eventually_training_loss hη (2*C+4) (1/1000000) (by linarith) (by norm_num),
    eventually_exceptional_training hη (2*C+4) (by linarith),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/40)),
    hK,eventually_ge_atTop (1:ℝ)] with σ hcover hbud hgrid hPu hloss herr hτsmall hK hσ
  intro q _ hq hx D R had U n b τ hn hnu hnupper hnlarge hb hbu hτ hτu
  let P := scaleP σ η D R
  let L := Real.toNNReal (scaleL σ η D)
  let g := log (n:ℝ)-3*σ/2
  let J := ⌈exp (7*σ/10)⌉₊
  let M := ⌈2*(q:ℝ)*P⌉₊
  have hσ0 : 0 < σ := by linarith
  have hqp : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hxlog : log (q:ℝ) = σ := by rw [←hx,log_exp]
  have hNgrid : ((Nat.log 2 n+2:ℕ):ℝ) ≤ σ^2 := hgrid q 2 n hqp hxlog le_rfl hn hnupper
  obtain ⟨p,h,hpupper,hbudget⟩ := hbud D R (Nat.log 2 n+2) had hNgrid
  have hP0 : 0 ≤ P := by have := hbudget.large; dsimp [P]; linarith
  have hL0 : 0 ≤ scaleL σ η D := (L_pos hσ0 had).le
  have hLP : scaleL σ η D ≤ P := by
    have hR : (1:ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by have := hbudget.Rlarge; omega)
    dsimp [P,scaleP]
    exact le_mul_of_one_le_right hL0 hR
  have hKlow : 1 ≤ scaleKstar σ η D := by
    apply hK.trans
    unfold scaleKstar
    have hh := mul_le_mul_of_nonneg_right had.D_lower (rpow_nonneg hσ0.le (6*beta η))
    rw [←rpow_add hσ0] at hh
    simpa only [show beta η+6*beta η=7*beta η by ring] using hh
  have hb' : b+log 2 ≤ (2*C+4)*scaleKstar σ η D := by
    have hl : log 2 ≤ (2:ℝ) := (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    nlinarith
  have hτ' : 2*τ ≤ (2*C+4)*σ^(-100*beta η) := by
    have hp : 0 ≤ σ^(-100*beta η) := rpow_nonneg hσ0.le _
    nlinarith
  have hl := hloss D R had (b+log 2) (2*τ) hb' hτ'
  have he := herr D R had (b+log 2) (2*τ) hb' hτ'
  have hPg : σ^beta η ≤ P := by
    apply (rpow_le_rpow_of_exponent_le hσ (by linarith : beta η ≤ 9*beta η)).trans
    exact (scale_bounds hσ hη had).1.trans hLP
  have hPupper : P ≤ σ/40 := by
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using hPu D R had
  have hgu : g ≤ σ/2+log 2 := by
    have hh := log_le_log hnp hnupper
    rw [log_mul (by norm_num) (pow_ne_zero _ hqp.ne'),log_pow,hxlog] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [g]
    linarith
  have hgn : (n:ℝ) = exp (3*σ/2+g) := by
    dsimp [g]
    rw [show 3*σ/2+(log (n:ℝ)-3*σ/2)=log (n:ℝ) by ring,exp_log hnp]
  have hJ : exp (σ/2-2*g/15) ≤ J := by
    apply le_trans _ (Nat.le_ceil (exp (7*σ/10)))
    apply exp_le_exp.mpr
    have hh : 0 ≤ log (n:ℝ) := log_nonneg (by exact_mod_cast hn)
    dsimp [g]
    linarith
  have hms : ∀ m, 0 < m → m ≤ n → n ≤ 2*m →
      Budget σ P L R (Nat.log 2 m+2) p h := by
    intro m _ hmn _
    exact hbudget.mono_grid (Nat.add_le_add_right (Nat.log_mono_right hmn) 2)
  have hl' : b+log 2+4*P*τ ≤ P/1000000 := by
    have hm := mul_le_mul_of_nonneg_right hLP (by norm_num : (0:ℝ) ≤ 1/1000000)
    dsimp [P] at *
    nlinarith
  have he' : 50000*exp (-(95/100:ℝ)*(L:ℝ)) ≤ exp (-(b+log 2)-4*P*τ)/800 := by
    dsimp only [L]
    rw [coe_toNNReal _ hL0]
    simpa only [show (2:ℝ)*scaleP σ η D R*(2*τ)=4*P*τ by dsimp [P]; ring] using he
  exact hcover q hq hx U n J P g b τ L R p h M hn hnu hPg hPupper hgu
    hbudget.p_pos hpupper hgn hJ hms hb hτ (hτu.trans hτsmall.le) hnlarge hl' he' (Nat.le_ceil _)

end
end SharpLogRamsey.SpatialPublic

end

end OAI
