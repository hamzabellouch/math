import Mathlib
import OAI.Analysis.Conductivity.Fourier.PureModeFamilyLocalCorrection
import OAI.Analysis.Conductivity.Fourier.AngularLocalizedMoments

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma correctionBox_convex (a b : Coord3) : Convex ℝ (correctionBox a b) := by
  have he : correctionBox a b=Set.univ.pi (fun i => Ioo (a i) (b i)) := by
    ext x
    simp only [mem_correctionBox,Set.mem_pi,mem_univ,true_implies,mem_Ioo]
  rw [he]
  exact convex_pi (fun _ _ => convex_Ioo _ _)

theorem periodic_pure_mode_family_correction
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k T l a b d : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0) (hT : 0<T)
    (hla : l<a) (hbd : b<d)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    (hup : ∀ q,AngularPeriodic T (fun y => ![u (q,y),v (q,y)]))
    {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    (hrz : ∀ j x,r j (p,x)=0)
    (hrp : ∀ j q,AngularPeriodic T (fun x => r j (q,x)))
    (hrs : ∀ j q,tsupport (fun x => r j (q,x))⊆{x | x 0∈Icc a b})
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,periodicSourceMoment T (fun y => ![u (q,y),v (q,y)]) (fun j y => r j (q,y))=0 →
      ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic T H ∧
        tsupport H⊆{x | x 0∈Icc l d} ∧ (∀ x,(H x).IsSymm) ∧
        (∀ j,symmetricSource H (fun y => ![u (q,y),v (q,y)]) j=(fun y => r j (q,y))) ∧
        ∀ x,‖H x‖≤ε := by
  let L : Coord3 := ![l,-T-1,-T-1]
  let D : Coord3 := ![d,T+1,T+1]
  let U := correctionBox L D
  let K : Set Coord3 := Icc ![a,-T,-T] ![b,T,T]
  let R : Fin 2 → P×Coord3 → ℝ := fun j z => angularCutoff T z.2*r j z
  have hKU : K⊆U := by
    intro x hx
    apply mem_correctionBox.mpr
    intro i
    fin_cases i
    · exact ⟨hla.trans_le (hx.1 0),(hx.2 0).trans_lt hbd⟩
    · have h1 : -T≤x 1 ∧ x 1≤T := ⟨hx.1 1,hx.2 1⟩
      constructor <;> dsimp [L,D] <;> linarith [h1.1,h1.2]
    · have h2 : -T≤x 2 ∧ x 2≤T := ⟨hx.1 2,hx.2 2⟩
      constructor <;> dsimp [L,D] <;> linarith [h2.1,h2.2]
  have hR : SmoothVanishingPairFamily p U R := by
    refine ⟨fun j => ((angularCutoff_smooth T).comp contDiff_snd).mul (hr j),?_,K,isCompact_Icc,hKU,?_⟩
    · intro j x
      dsimp [R]
      rw [hrz,mul_zero]
    · intro q j
      exact angularCutoff_compact_support hT (hrs j q)
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc L D)).isBounded.exists_norm_le
  obtain ⟨M,hM,hMp⟩ := angularPeriodize_uniform_bound (E:=Mat3) hT B
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hεM : 0<ε/M := div_pos hε hMr
  have hc := pure_mode_family_correction hu hv p hσ hlam hk hub hvb
    (correctionBox_isOpen L D) (correctionBox_convex L D).isPreconnected hR hεM
  filter_upwards [hc] with q hq
  intro hm
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => ![u (q,y),v (q,y)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact hu.comp (contDiff_const.prodMk contDiff_id)
    · exact hv.comp (contDiff_const.prodMk contDiff_id)
  have hmo : physicalSourceMoment (fun y => ![u (q,y),v (q,y)]) (fun j y => R j (q,y))=0 := by
    exact (physicalSourceMoment_angularCutoff (r:=fun j x => r j (q,x)) hT hF.continuous (hup q)
      (fun j => ((hr j).comp (contDiff_const.prodMk contDiff_id)).continuous)
      (fun j => hrp j q) (fun j => hrs j q)).trans hm
  obtain ⟨H,hH,hHc,hHs,hHsy,hHr,hHb⟩ := hq hmo
  have hnorm : ∀ x,H x≠0 → ‖x‖≤B := by
    intro x hx
    apply hB x
    have hh := mem_correctionBox.mp (hHs (subset_tsupport H hx))
    exact ⟨fun i => (hh i).1.le,fun i => (hh i).2.le⟩
  have hax : tsupport H⊆{x | x 0∈Icc l d} := by
    intro x hx
    have hh := mem_correctionBox.mp (hHs hx) 0
    exact ⟨hh.1.le,hh.2.le⟩
  refine ⟨angularPeriodize T H,angularPeriodize_smooth hT hH hHc,
    angularPeriodize_periodic T H,angularPeriodize_axial_support hax,
    angularPeriodize_symmetric hT hHc hHsy,?_,?_⟩
  · intro j
    funext x
    rw [symmetricSource_angularPeriodize hT hH hHc hF (hup q),hHr j]
    exact congrFun (angularCutoff_periodize hT (hrp j q)) x
  · intro x
    have hh := hMp H (ε/M) hεM.le hnorm hHb x
    have he : (M:ℝ)*(ε/M)=ε := by field_simp
    rwa [he] at hh

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma flatPhaseMode_angularPeriodic (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ) :
    AngularPeriodic (2*Real.pi) (flatPhaseMode s h phase) := by
  intro n x
  have he : torusAngular h (x+angularShift (2*Real.pi) n)+phase=
      torusAngular h x+phase+(h 0*n 0+h 1*n 1:ℤ)*(2*Real.pi) := by
    change (h 0:ℝ)*(x 1+2*Real.pi*(n 0:ℝ))+(h 1:ℝ)*(x 2+2*Real.pi*(n 1:ℝ))+phase=
      (h 0:ℝ)*x 1+(h 1:ℝ)*x 2+phase+(h 0*n 0+h 1*n 1:ℤ)*(2*Real.pi)
    push_cast
    ring
  change exp (-torusRate s h*(x 0+0))*cos (torusAngular h (x+angularShift (2*Real.pi) n)+phase)=_
  rw [add_zero,he,cos_add_int_mul_two_pi]
  rfl

lemma flatFourier_angularPeriodic (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) :
    AngularPeriodic (2*Real.pi) (flatFourier s a phase) := by
  intro n x
  unfold flatFourier
  apply tsum_congr
  intro h
  rw [flatPhaseMode_angularPeriodic s h (phase h) n x]

lemma compactifiedFourierTail_angularPeriodic (s : Fin 3 → ℝ) (lam T0 : ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (p : ℝ) :
    AngularPeriodic (2*Real.pi) (fun x => compactifiedFourierTail s lam T0 a phase (p,x)) := by
  intro n x
  unfold compactifiedFourierTail
  apply tsum_congr
  intro h
  dsimp [compactifiedFourierTerm]
  have he : x+angularShift (2*Real.pi) n+![T0,0,0]=(x+![T0,0,0])+angularShift (2*Real.pi) n := by abel
  rw [he,flatPhaseMode_angularPeriodic]

lemma exists_normalized_periodic_end_cutoff {R T0 δ : ℝ} (hT : δ-T0 < -R) :
    ∃ ρ : (ℝ×Coord3)→ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ρ ∧
      tsupport ρ⊆Ioo (-1) 1 ×ˢ {x : Coord3 | δ-T0<x 0} ∧
      (∀ z,ρ z∈Icc 0 1) ∧ (∀ p T,AngularPeriodic T (fun x => ρ (p,x))) ∧
      (∀ p∈Icc (-(1:ℝ)/2) (1/2),∀ x : Coord3, x 0∈Icc (-R) R → ρ (p,x)=1) := by
  let K : Set (ℝ×ℝ) := Icc (-(1:ℝ)/2) (1/2) ×ˢ Icc (-R) R
  let Ω : Set (ℝ×ℝ) := Ioo (-1) 1 ×ˢ Ioo (δ-T0) (R+1)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_Ioo
  have hb : Bornology.IsBounded Ω :=
    ((isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).isBounded.subset Ioo_subset_Icc_self).prod
      ((isCompact_Icc : IsCompact (Icc (δ-T0) (R+1))).isBounded.subset Ioo_subset_Icc_self)
  have hsub : K⊆Ω := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
      ⟨hT.trans_le hz.2.1,by linarith [hz.2.2]⟩⟩
  obtain ⟨χ,hχ,hχc,hχs,hχb,hχ1⟩ := exists_smooth_core_cutoff hK hΩ hb hsub
  let Q : (ℝ×Coord3)→(ℝ×ℝ) := fun z => (z.1,z.2 0)
  have hQ : ContDiff ℝ (↑(⊤:ℕ∞)) Q := by dsimp [Q]; fun_prop
  refine ⟨χ ∘ Q,hχ.comp hQ,?_,fun z => hχb _,?_,?_⟩
  · intro z hz
    have he := hχs (tsupport_comp_subset_preimage χ hQ.continuous hz)
    exact ⟨he.1,he.2.1⟩
  · intro p T n x
    change χ (p,x 0+0)=χ (p,x 0)
    rw [add_zero]
  · intro p hp x hx
    exact (hχ1 (p,x 0) ⟨hp,hx⟩).self_of_nhds

theorem exists_smooth_periodic_normalized_tail {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {lam T0 gap B δ R : ℝ} {a phase : (Fin 2→ℤ)→ℝ}
    (hg : 0<gap) (hB : 0≤B) (ha : ∀ h,|a h|≤B) (hδ : 0<δ)
    (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h) (hT : δ-T0 < -R) :
    ∃ f : (ℝ×Coord3)→ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) f ∧
      (∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x))) ∧
      (∀ p≤0,∀ x,f (p,x)=0) ∧
      (∀ p∈Ioc 0 (1/2),∀ x : Coord3,x 0∈Icc (-R) R →
        f (p,x)=exp (lam*(T0+1/p))*flatFourier s a phase (x+![T0+1/p,0,0])) := by
  obtain ⟨ρ,hρ,hρs,hρb,hρp,hρ1⟩ := exists_normalized_periodic_end_cutoff hT
  have hr' : ∀ h,a h≠0 → lam<torusRate s h := fun h hh => by linarith [hr h hh]
  refine ⟨fun z => ρ z*compactifiedFourierTail s lam T0 a phase z,
    smooth_mul_of_support_in_open (isOpen_Ioo.prod (axial_halfspace_open _))
      (compactifiedFourierTail_smooth hs hg hB ha hδ hr) hρ hρs,?_,?_,?_⟩
  · intro p n x
    dsimp only
    exact congrArg₂ (· * ·) (hρp p (2*Real.pi) n x)
      (compactifiedFourierTail_angularPeriodic s lam T0 a phase p n x)
  · intro p hp x
    dsimp only
    rw [compactifiedFourierTail_of_nonpos hr' hp,mul_zero]
  · intro p hp x hx
    dsimp only
    rw [hρ1 p ⟨by linarith [hp.1],hp.2⟩ x hx,one_mul,compactifiedFourierTail_of_pos hr' hp.1]

end ScalarConductivity

end
end

end OAI
