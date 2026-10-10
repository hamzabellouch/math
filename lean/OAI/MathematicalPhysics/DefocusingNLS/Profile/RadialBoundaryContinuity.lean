import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeParameterStart

namespace OAI

/-! Sequential continuity of the free boundary value and modulus, with varying start radius. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem radial_free_boundary_tendsto (u b l : ℝ) (bn ln : ℕ → ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hbn : ∀ n, bn n ∈ Icc (334/1000 : ℝ) (335/1000))
    (hl : (3 : ℝ) ≤ l) (hln : ∀ n, (3 : ℝ) ≤ ln n) (hu : u ≤ (10/3 : ℝ))
    (hlu : l ≤ u) (hlnu : ∀ n, ln n ≤ u)
    (hw : u-l ≤ (1/1000 : ℝ)) (hwn : ∀ n, u-ln n ≤ (1/1000 : ℝ))
    (hbT : Tendsto bn atTop (𝓝 b)) (hlT : Tendsto ln atTop (𝓝 l))
    (F G : ℝ → ℂ) (Fn Gn : ℕ → ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hFn : ∀ n, Continuous (Fn n))
    (hGn : ∀ n, Continuous (Gn n))
    (hFI : ∀ r ∈ Icc l u, F r=1+∫ t in l..r, G t)
    (hGI : ∀ r ∈ Icc l u, G r=∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hFIn : ∀ n r, r ∈ Icc (ln n) u → Fn n r=1+∫ t in (ln n)..r, Gn n t)
    (hGIn : ∀ n r, r ∈ Icc (ln n) u → Gn n r=∫ t in (ln n)..r,
      -radialFreeCoefficient t*Gn n t-(bn n : ℂ)*Fn n t)
    (hB : ∀ r ∈ Icc l u, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2)
    (hBn : ∀ n r, r ∈ Icc (ln n) u → ‖Fn n r‖ ≤ 2 ∧ ‖Gn n r‖ ≤ 2) :
    Tendsto (fun n => (Fn n u,Gn n u)) atTop (𝓝 (F u,G u)) ∧
      Tendsto (fun n => ‖Fn n u‖) atTop (𝓝 ‖F u‖) := by
  have hs : Tendsto (fun n => |ln n-l|+|bn n-b|) atTop (𝓝 0) := by
    convert (hlT.sub_const l).abs.add (hbT.sub_const b).abs using 1; simp
  have hnorm : Tendsto (fun n => ‖(Fn n u,Gn n u)-(F u,G u)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) _ hs
    intro n
    exact radial_free_endpoint_difference (bn n) b (ln n) l u (hbn n) hb (hln n) hl hu
      (hlnu n) hlu (hwn n) hw (Fn n) (Gn n) F G (hFn n) (hGn n) hF hG
      (hFIn n) (hGIn n) hFI hGI (hBn n) hB
  have hT : Tendsto (fun n => (Fn n u,Gn n u)) atTop (𝓝 (F u,G u)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hTF : Tendsto (fun n => Fn n u) atTop (𝓝 (F u)) :=
    (continuous_fst.tendsto (F u,G u)).comp hT
  exact ⟨hT,hTF.norm⟩

end DefocusingNLS

end OAI
