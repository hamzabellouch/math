import Mathlib
import OAI.Analysis.Conductivity.Variational.SmoothFamilyGlobalCorrection
import OAI.Analysis.Conductivity.Walls.SimpleCriticalWallRegion

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma pureWallMode_shift_wall {σ lam k a : ℝ} (ha : sin (k*a)=0) (y : Coord3) :
    pureWallMode σ lam k (boxCoordinates (y+![0,0,a]))=
      pureWallMode (σ*cos (k*a)) lam k (boxCoordinates y) := by
  change σ*exp (-lam*(y 0+0))*cos (k*(y 2+a))=
    (σ*cos (k*a))*exp (-lam*y 0)*cos (k*y 2)
  rw [add_zero,mul_add,cos_add,ha,mul_zero,sub_zero]
  ring

theorem exists_pure_mode_critical_family_region
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    {x : Coord3} (hxz : sin (k*x 2)=0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    ∃ B : VanishingCorrectionRegion (fun z => ![u z,v z]) p U,x∈B.region := by
  let a : Coord3 := ![0,0,x 2]
  let τ : P×Coord3 → P×Coord3 := fun z => (z.1,z.2+a)
  have hτ : ContDiff ℝ (↑(⊤:ℕ∞)) τ := contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  let ut := u∘τ
  let vt := v∘τ
  have hut : ∀ y,ut (p,y)=y 0 := by
    intro y
    change u (p,y+a)=y 0
    rw [hub]
    change y 0+0=y 0
    exact add_zero _
  have hvt : ∀ y,vt (p,y)=pureWallMode (σ*cos (k*x 2)) lam k (boxCoordinates y) := by
    intro y
    exact (hvb (y+a)).trans (pureWallMode_shift_wall hxz y)
  have hcos : cos (k*x 2)≠0 := by
    intro h
    have hh := sin_sq_add_cos_sq (k*x 2)
    rw [hxz,h] at hh
    norm_num at hh
  let Y₀ := ((Homeomorph.refl P).prodCongr (Homeomorph.subRight a)).toOpenPartialHomeomorph
  let Y := Y₀.restr (univ×ˢU)
  have hYs : Y.source=univ×ˢU := by
    simp only [Y,OpenPartialHomeomorph.restr_source,(isOpen_univ.prod hU).interior_eq]
    exact univ_inter _
  have hY : ∀ q y,(Y (q,y)).1=q := fun _ _ => rfl
  have hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y := contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)
  have hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target :=
    (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contDiffOn
  have hpot : ∀ z∈Y.source,![ut (z.1,(Y z).2),vt (z.1,(Y z).2)]=![u z,v z] := by
    intro z _
    change ![u (z.1,z.2-a+a),v (z.1,z.2-a+a)]=![u z,v z]
    rw [sub_add_cancel]
  have huv : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => ![u z,v z]) :=
    contDiff_pi.mpr (by intro i; fin_cases i; exact hu; exact hv)
  have htv : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => ![ut z,vt z]) := huv.comp hτ
  apply exists_transported_vanishing_region huv htv p Y hY hsm hinv
    (hYs ▸ Subset.rfl) (hYs ▸ (show (p,x)∈univ×ˢU from ⟨mem_univ _,hx⟩)) hpot
  intro A hA hxA
  apply exists_simple_critical_wall_region (hu.comp hτ) (hv.comp hτ) p
    (mul_ne_zero hσ hcos) hlam hk hut hvt (x := x-a) (by simp [a]) hA hxA

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma pureWallMode_pair_regular {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0)
    {x : Coord3} (hx : sin (k*x 2)≠0) :
    Function.Surjective (fderiv ℝ (wallCoordinatePair (pureWallMode σ lam k)) x) := by
  apply wallCoordinatePair_surjective ((pureWallMode_smooth σ lam k).differentiable (by simp))
  rw [pureWallMode_normalDerivative]
  exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) (mul_ne_zero (neg_ne_zero.mpr hx) hk)

lemma exists_sin_ne_zero_in_open {k : ℝ} (hk : k≠0)
    {O : Set Coord3} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ x∈O,sin (k*x 2)≠0 := by
  obtain ⟨x,hx⟩ := hne
  by_cases hs : sin (k*x 2)=0
  · obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO x hx
    let δ := min ε (Real.pi/|k|)/2
    have hak : 0 < |k| := abs_pos.mpr hk
    have hδ : 0<δ := by dsimp [δ]; positivity
    have hδε : δ<ε := by dsimp [δ]; linarith [min_le_left ε (Real.pi/|k|)]
    have hδpi : δ<Real.pi/|k| := by
      dsimp [δ]
      linarith [min_le_right ε (Real.pi/|k|),div_pos Real.pi_pos hak]
    let y : Coord3 := x+![0,0,δ]
    have hy : y∈O := by
      apply hball
      rw [Metric.mem_ball,dist_pi_lt_iff hε]
      intro i
      fin_cases i
      · change dist (x 0+0) (x 0)<ε
        simpa only [add_zero,dist_self] using hε
      · change dist (x 1+0) (x 1)<ε
        simpa only [add_zero,dist_self] using hε
      · change dist (x 2+δ) (x 2)<ε
        simpa only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hδ] using hδε
    have hcos : cos (k*x 2)≠0 := by
      intro h
      have hh := sin_sq_add_cos_sq (k*x 2)
      rw [hs,h] at hh
      norm_num at hh
    refine ⟨y,hy,?_⟩
    change sin (k*(x 2+δ))≠0
    rw [mul_add,sin_add,hs,zero_mul,zero_add]
    apply mul_ne_zero hcos
    apply sin_ne_zero_of_abs_lt_pi (mul_ne_zero hk hδ.ne')
    rw [abs_mul,abs_of_pos hδ]
    simpa only [mul_comm] using (lt_div_iff₀ hak).mp hδpi
  · exact ⟨x,hx,hs⟩

theorem pure_mode_family_correction
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    {U : Set Coord3} (hU : IsOpen U) (hUc : IsPreconnected U)
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p U r)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => ![u (q,y),v (q,y)]) (fun j y => r j (q,y))=0 →
      BoundedPhysicallyCorrectable (fun y => ![u (q,y),v (q,y)]) U (fun j y => r j (q,y)) ε := by
  let F : P×Coord3 → Fin 2 → ℝ := fun z => ![u z,v z]
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) F :=
    contDiff_pi.mpr (by intro i; fin_cases i; exact hu; exact hv)
  have hFb : (fun y => F (p,y))=wallCoordinatePair (pureWallMode σ lam k) := by
    funext y j
    fin_cases j
    · exact hub y
    · exact hvb y
  have hreg {y : Coord3} (hy : sin (k*y 2)≠0) :
      Function.Surjective (fderiv ℝ (fun y => F (p,y)) y) := by
    rw [hFb]
    exact pureWallMode_pair_regular hσ hk hy
  have hcover : (⋃ B : VanishingCorrectionRegion F p U,B.region)=U := by
    apply Subset.antisymm (iUnion_subset (fun B => B.region_subset))
    intro x hx
    by_cases hs : sin (k*x 2)=0
    · obtain ⟨B,hB⟩ := exists_pure_mode_critical_family_region hu hv p hσ hlam hk hub hvb hs hU hx
      exact mem_iUnion.mpr ⟨B,hB⟩
    · obtain ⟨B,hB⟩ := exists_parametric_correction_box hF p hU hx (hreg hs)
      exact mem_iUnion.mpr ⟨B.toVanishing p,hB⟩
  apply global_vanishing_family_correction hF p hUc hcover ?_ hr hε
  intro O hO hne _
  obtain ⟨x,hx,hs⟩ := exists_sin_ne_zero_in_open hk hO hne
  exact ⟨x,hx,hreg hs⟩

end ScalarConductivity

end
end

end OAI
