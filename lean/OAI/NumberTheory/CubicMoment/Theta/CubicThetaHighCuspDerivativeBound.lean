import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighCuspRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspLatticeWeight

namespace OAI

/-! The actual high-cusp row derivatives have a summable lattice
majorant, with one inverse height gained by differentiation. -/
noncomputable section
open Set Filter
open scoped MatrixGroups Topology
namespace CubicFirstMoment

lemma cubicThetaHighCuspRow_fderiv_lattice_bound
    (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow) {p : ℂ × ℝ} {R : ℝ}
    (hp : 2≤p.2) (hR : Complex.normSq p.1≤R) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p‖≤
      (6*(3+2*R)^2*cubicThetaFirstJetConstant s*p.2^(3-s.re))*cubicThetaCuspLatticeWeight δ s r := by
  have hp0 : 0<p.2 := by linarith
  have hd := cubicThetaHighCuspRow_fderiv_bound δ r s hp0
  rw [cubicThetaHighCuspRow_eq δ r hp s] at hd
  have hb := cubicThetaRemainderRow_cusp_bound δ r p.1 hp hR hs
  have hJ : 0≤cubicThetaFirstJetConstant s/p.2 := div_nonneg (cubicThetaJetConstants_nonneg s).1 hp0.le
  have he : p.2^(4-s.re)/p.2=p.2^(3-s.re) := by
    rw [← Real.rpow_sub_one hp0.ne']
    congr 1
    ring
  calc
    _ ≤ 3*(‖cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) p) s‖*
        (cubicThetaFirstJetConstant s/p.2)) := hd
    _ ≤ 3*(((2*(3+2*R)^2*p.2^(4-s.re))*
        norm (cubicThetaCuspRow δ r).c^(-(s.re-2))*(1+norm (cubicThetaCuspRow δ r).d)^(-2:ℝ))*
        (cubicThetaFirstJetConstant s/p.2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hJ) (by norm_num)
    _ = (6*(3+2*R)^2*cubicThetaFirstJetConstant s*cubicThetaCuspLatticeWeight δ s r)*
        (p.2^(4-s.re)/p.2) := by unfold cubicThetaCuspLatticeWeight; ring
    _ = _ := by rw [he]; ring

lemma cubicThetaHighCuspRow_local_fderiv_bound
    (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3<s.re) {p : ℂ × ℝ} (hp : 2<p.2) :
    ∃ r : ℝ, 0<r ∧ ∃ u : CubicThetaBottomRow → ℝ, Summable u ∧
      ∀ b q, q∈Metric.ball p r → 2<q.2 ∧
        ‖fderiv ℝ (fun z => cubicThetaHighCuspRow δ b z s) q‖≤u b := by
  let R := Complex.normSq p.1+1
  let H := p.2^(3-s.re)+1
  have hp0 : 0<p.2 := by linarith
  have hN : ContinuousAt (fun q : ℂ × ℝ => Complex.normSq q.1) p :=
    Complex.continuous_normSq.continuousAt.comp continuousAt_fst
  have hV : ContinuousAt (fun q : ℂ × ℝ => q.2^(3-s.re)) p :=
    continuousAt_snd.rpow_const (Or.inl hp0.ne')
  have hU : {q : ℂ × ℝ | 2<q.2 ∧ Complex.normSq q.1<R ∧ q.2^(3-s.re)<H}∈𝓝 p :=
    (continuous_snd.continuousAt.eventually_const_lt hp).and
      ((hN.eventually_lt_const (by dsimp [R]; linarith)).and
        (hV.eventually_lt_const (by dsimp [H]; linarith)))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hU
  let C := 6*(3+2*R)^2*cubicThetaFirstJetConstant s
  have hC : 0≤C := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (cubicThetaJetConstants_nonneg s).1
  let u := fun b => (C*H)*cubicThetaCuspLatticeWeight δ s b
  refine ⟨r,hr,u,(cubicThetaCuspLatticeWeight_summable δ hs).mul_left _,?_⟩
  intro b q hq
  obtain ⟨hqv,hqR,hqH⟩ := hsub hq
  refine ⟨hqv,?_⟩
  have hd := cubicThetaHighCuspRow_fderiv_lattice_bound δ b hqv.le hqR.le (by linarith : 2 ≤ s.re)
  exact hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqH.le hC)
    (cubicThetaCuspLatticeWeight_nonneg δ s b))

end CubicFirstMoment

end

end OAI
