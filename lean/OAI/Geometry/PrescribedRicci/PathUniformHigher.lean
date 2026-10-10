import Mathlib
import OAI.Geometry.PrescribedRicci.PathLocalGain
import OAI.Geometry.PrescribedRicci.PathUniformAtlas
import OAI.Geometry.PrescribedRicci.PathUniformForcing
import OAI.Geometry.PrescribedPotential.RegularityCutoffs

namespace OAI

/-! Path Uniform Higher. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
  {g : KaehlerMetric A}

omit [ConnectedSpace X] in
lemma weighted_cutoff_reconstruction (i : Fin A.count) (w F : Smooth A)
    (hw : tsupport (w : X → ℂ) ⊆ (A.euclideanChart i).source)
    (κ : ChartCutoff (A.euclideanChart i).target)
    (hκ : ∀ x ∈ tsupport (w : X → ℂ), κ (A.euclideanChart i x) = 1) :
    globalize i (κ.mulOn (A.euclideanChart i).open_target (w.smooth i))
      (localize A i (cutoffGlobal i κ) (cutoffGlobal_support i κ) F) = w.mul F := by
  ext x
  rw [globalize_apply,localize_cutoff_product]
  by_cases hx : x ∈ (A.euclideanChart i).source
  · rw [ite_eq_left hx]
    change (κ (A.euclideanChart i x)*w ((A.euclideanChart i).symm (A.euclideanChart i x)))*
      (κ (A.euclideanChart i x)*F ((A.euclideanChart i).symm (A.euclideanChart i x))) = w x*F x
    rw [(A.euclideanChart i).left_inv hx]
    by_cases hwx : w x = 0
    · rw [hwx]; ring
    · rw [hκ x (subset_tsupport _ hwx),one_mul,one_mul]
  · rw [ite_eq_right hx]
    change 0 = w x*F x
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hw hs)),zero_mul]

namespace GluingData
variable (D : GluingData g ι)

lemma path_patch_gain (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d)
    (p : UniformPathPatch g line) (κ : ChartCutoff (A.euclideanChart p.index).target)
    (hκp : tsupport (κ : EC d → ℂ) ⊆ p.domain) (hκr : ∀ y, (κ y).im = 0)
    (k : ℕ) (hk : 1 ≤ k)
    (hprev : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed ((k:ℝ)+1) (Smooth.ofReal z.potential)‖ ≤ C) :
    UniformSobolev ((k:ℝ)+2) (fun z : g.NormalizedPathSolution line =>
      localize A p.index (cutoffGlobal p.index κ) (cutoffGlobal_support p.index κ) (Smooth.ofReal z.potential)) := by
  obtain ⟨σ,_,hσ⟩ := exists_chartCutoff_nhds κ.compact (A.euclideanChart p.index).open_target κ.support_sub
  obtain ⟨τ,hτr,hτ⟩ := exists_chartCutoff_nhds σ.compact (A.euclideanChart p.index).open_target σ.support_sub
  exact D.path_local_gain line hd p κ σ τ hκp hκr hτr hσ hτ k hk hprev

lemma volumePath_uniform_gain (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d)
    (k : ℕ) (hk : 1 ≤ k)
    (hprev : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed ((k:ℝ)+1) (Smooth.ofReal z.potential)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed ((k:ℝ)+2) (Smooth.ofReal z.potential)‖ ≤ C := by
  obtain ⟨S,L,hLI,hLS⟩ := exists_uniform_path_localizers g line hd
  have hc (p : S) : ∃ κ : ChartCutoff (A.euclideanChart p.val.index).target,
      tsupport (κ : EC d → ℂ) ⊆ p.val.domain ∧ (∀ y, (κ y).im = 0) ∧
      ∀ x ∈ tsupport (L.weight p : X → ℂ), κ (A.euclideanChart p.val.index x) = 1 := by
    let e := A.euclideanChart p.val.index
    have hK : IsCompact (e '' tsupport (L.weight p : X → ℂ)) :=
      (isClosed_tsupport _).isCompact.image_of_continuousOn
        (e.continuousOn.mono (fun x hx => (hLS p hx).1))
    have hKU : e '' tsupport (L.weight p : X → ℂ) ⊆ p.val.domain := by
      rintro y ⟨x,hx,rfl⟩
      exact (hLS p hx).2
    obtain ⟨κ,hκr,hκ⟩ := exists_chartCutoff_nhds hK p.val.isOpen_domain hKU
    exact ⟨⟨κ.val,κ.compact,κ.support_sub.trans p.val.domain_sub⟩,κ.support_sub,hκr,
      fun x hx => (hκ _ ⟨x,hx,rfl⟩).eq_of_nhds⟩
  choose κ hκp hκr hκ using hc
  have hlocal (p : S) := D.path_patch_gain line hd p.val (κ p) (hκp p) (hκr p) k hk hprev
  choose B hB hb using hlocal
  let η (p : S) := (κ p).mulOn (A.euclideanChart p.val.index).open_target ((L.weight p).smooth p.val.index)
  have hglob (p : S) := globalize_integer_bound D.localizers p.val.index (η p) (k+2)
  choose Q hQ hq using hglob
  have hsum (F : Smooth A) : F = ∑ p : S, globalize p.val.index (η p)
      (localize A p.val.index (cutoffGlobal p.val.index (κ p)) (cutoffGlobal_support p.val.index (κ p)) F) := by
    have he (p : S) := weighted_cutoff_reconstruction p.val.index (L.weight p) F
      (by simpa only [hLI p] using L.support_sub p) (κ p) (hκ p)
    simp_rw [show ∀ p : S, globalize p.val.index (η p)
      (localize A p.val.index (cutoffGlobal p.val.index (κ p)) (cutoffGlobal_support p.val.index (κ p)) F) =
      (L.weight p).mul F from he]
    ext x
    change F.val x = (∑ p : S, (L.weight p).mul F).val x
    simp only [Submodule.coe_sum,Finset.sum_apply]
    change F x = ∑ p : S, L.weight p x*F x
    rw [← Finset.sum_mul,L.sum_one,one_mul]
  refine ⟨∑ p, Q p*B p,Finset.sum_nonneg (fun p _ => mul_nonneg (hQ p) (hB p)),fun z => ?_⟩
  rw [hsum (Smooth.ofReal z.potential),map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  have hh := hq p (localize A p.val.index (cutoffGlobal p.val.index (κ p))
    (cutoffGlobal_support p.val.index (κ p)) (Smooth.ofReal z.potential))
  rw [Nat.cast_add,Nat.cast_ofNat] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (hb p z) (hQ p))

theorem volumePath_uniform_all (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed (k:ℝ) (Smooth.ofReal z.potential)‖ ≤ C := by
  have hhigh : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed ((k:ℝ)+2) (Smooth.ofReal z.potential)‖ ≤ C := by
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero,zero_add]
      exact D.volumePath_uniform_H2 line hd
    | succ n ih =>
      have he : ((n+1:ℕ):ℝ)+1 = (n:ℝ)+2 := by push_cast; ring
      have h := D.volumePath_uniform_gain line hd (n+1) (by omega) (by rw [he]; exact ih)
      exact h
  intro k
  obtain ⟨C,hC,hc⟩ := hhigh k
  obtain ⟨B,hB,hb⟩ := D.localizers.boundedCore_lower (by linarith : (k:ℝ) ≤ (k:ℝ)+2)
  refine ⟨B*C,mul_nonneg hB hC,fun z => ?_⟩
  exact (hb (Smooth.ofReal z.potential)).trans (mul_le_mul_of_nonneg_left (hc z) hB)
end GluingData
end GlobalElliptic

end
end

end OAI
