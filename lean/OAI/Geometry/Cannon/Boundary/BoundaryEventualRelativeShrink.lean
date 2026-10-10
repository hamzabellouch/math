import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryPackingRelativeTests
import OAI.Geometry.Cannon.Modulus.ModulusFamilyMono
import OAI.Geometry.Cannon.Uniformization.EventualRelativeShrink

namespace OAI

section
noncomputable section
namespace CannonRelease
open Set Metric Filter Topology CannonGraph CannonVisual CannonMobius CannonCells CannonUniformization
open CannonRealization

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_eventual_relative_shrink (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ F : ℕ → C(Boundary D,Sphere),(∀ n,Function.Surjective (F n)) ∧
      EventualRelativeShrink F := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨L,LI,σ,s,r₀,Z,hL,hLI,hσ,hσ1,hs,hr₀,hZ,V,hV,htests⟩ :=
    boundary_packing_relative_tests D hδ φ
  obtain ⟨T,hT,hmod⟩ := boundary_annular_modulus_smallness D hδ φ
  let α := Real.exp (2*visualExponent δ)
  have hα : 1<α := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  let mesh : ℕ → ℝ := fun n => (α^n)⁻¹
  have hmpos (n : ℕ) : 0 < mesh n := inv_pos.mpr (pow_pos (zero_lt_one.trans hα) _)
  have hmt : Tendsto mesh atTop (𝓝 0) := by
    simpa only [mesh,inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_pos.mpr (zero_lt_one.trans hα)).le (inv_lt_one_of_one_lt₀ hα)
  have hmaps : ∀ n : ℕ, ∃ g : C(Boundary D,Sphere),Function.Surjective g ∧
      (mesh n ≤ r₀ → (∀ x y,g x=g y → dist x y ≤ 2*(L*mesh n)) ∧
      ∀ (o a b : Boundary D) (r R ε : ℝ),0<r → 0<R → R ≤ s →
        dist o a ≤ r → R ≤ dist o b → 0<dist (g o) (g b) → 0<ε →
        ε*dist (g o) (g b)<dist (g o) (g a) →
      V ε ≤ Z*modulus (fun i : T n =>ball i.val (2*mesh n)) (annulusFamily o (LI*r) (σ*R))) := by
    intro n
    by_cases hn : mesh n ≤ r₀
    · obtain ⟨g,hgs,hgf,hgc⟩ := htests (mesh n) (hmpos n) hn (T n) (hT n).1
        (fun x=>by obtain ⟨y,hy,hyx⟩ := (hT n).2 x; exact ⟨y,hy,by rwa [dist_comm]⟩)
      exact ⟨g,hgs,fun _=>⟨hgf,hgc⟩⟩
    · let g := φ.trans roundChart.symm
      exact ⟨⟨g,g.continuous⟩,g.surjective,fun h=>False.elim (hn h)⟩
  choose F hsurj hprops using hmaps
  refine ⟨F,hsurj,?_⟩
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hLIp : 0<LI := zero_lt_one.trans_le hLI
  have hdia1 : diam (univ : Set (Boundary D)) ≤ 1 :=
    diam_le_of_forall_dist_le zero_le_one (fun x _ y _=>boundaryDist_le_one D hδ x y)
  intro ε hε
  let tol := V ε/(Z+1)
  have htol : 0<tol := div_pos (hV ε hε) (by linarith)
  obtain ⟨ratio,hratio,hsmall⟩ := hmod tol htol
  have hratiop : 0<ratio := zero_lt_one.trans hratio
  let k := min 1 s
  have hk : 0<k := lt_min zero_lt_one hs
  let τ := σ*k/(ratio*LI)
  have hτ : 0<τ := div_pos (mul_pos hσ hk) (mul_pos hratiop hLIp)
  refine ⟨τ,hτ,?_⟩
  intro R hR
  by_cases hRD : R ≤ diam (univ : Set (Boundary D))
  · let S := min R s
    have hS : 0<S := lt_min hR hs
    have hSR : S ≤ R := min_le_left _ _
    have hSs : S ≤ s := min_le_right _ _
    have hR1 : R ≤ 1 := hRD.trans hdia1
    have hkR : k*R ≤ S := by
      apply le_min
      · exact mul_le_of_le_one_left hR.le (min_le_left _ _)
      · calc
          k*R ≤ s*R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
          _ ≤ s := mul_le_of_le_one_right hs.le hR1
    let outer := σ*S
    have hout : 0<outer := mul_pos hσ hS
    have houtR : outer ≤ R := (mul_le_of_le_one_left hS.le hσ1).trans hSR
    let r := (outer/ratio)/LI
    have hr : 0<r := div_pos (div_pos hout hratiop) hLIp
    have hrad : LI*r = outer/ratio := by dsimp [r]; field_simp
    have hnear : τ*R ≤ r := by
      calc
        τ*R = (σ*(k*R)/ratio)/LI := by dsimp [τ]; ring
        _ ≤ (σ*S/ratio)/LI := by gcongr
    have hgood : ∀ᶠ n : ℕ in atTop,mesh n ≤ r₀ :=
      (hmt.eventually (gt_mem_nhds hr₀)).mono (fun _ h=>h.le)
    have hfine : ∀ᶠ n : ℕ in atTop,mesh n < R/(2*L) :=
      hmt.eventually (gt_mem_nhds (div_pos hR (by positivity)))
    filter_upwards [hgood,hfine,hsmall outer hout (houtR.trans hRD)] with n hn hnf hnm
    intro o a b hoa hob
    have hden : 0<dist (F n o) (F n b) := by
      apply dist_pos.mpr
      intro heq
      have hf := (hprops n hn).1 o b heq
      have hm := (lt_div_iff₀ (show 0<2*L by positivity)).mp hnf
      nlinarith
    by_contra hfail
    have hcost := (hprops n hn).2 o a b r S ε hr hS hSs (hoa.trans hnear) (hSR.trans hob)
      hden hε (lt_of_not_ge hfail)
    rw [hrad] at hcost
    have hbound := mul_le_mul_of_nonneg_left (hnm o).le hZ
    have hid : tol*(Z+1)=V ε := by dsimp [tol]; field_simp
    nlinarith
  · filter_upwards [] with n o a b hoa hob
    exact False.elim (hRD (hob.trans (dist_le_diam_of_mem isCompact_univ.isBounded
      (mem_univ _) (mem_univ _))))
end CannonRelease

end
end

end OAI
