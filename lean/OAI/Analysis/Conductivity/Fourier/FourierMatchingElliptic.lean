import Mathlib
import OAI.Analysis.Conductivity.Fourier.FourierMatchingFamilyCorrection

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

lemma matrix_quadratic_elementwise_bound (H : Mat3) (v : Coord3) :
    |v ⬝ᵥ (H*ᵥv)| ≤ 3*‖H‖*(v ⬝ᵥ v) := by
  change |∑ i : Fin 3,v i*∑ j : Fin 3,H i j*v j| ≤ _
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin 3,∑ j : Fin 3,|v i*(H i j*v j)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3,∑ j : Fin 3,‖H‖*((v i)^2+(v j)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hh : |H i j|≤‖H‖ := by
        change ‖H i j‖≤‖H‖
        exact Matrix.norm_entry_le_entrywise_sup_norm H
      rw [abs_mul,abs_mul]
      have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg (abs_nonneg (v i)) (abs_nonneg (v j)))
      have hs := mul_nonneg (norm_nonneg H) (sq_nonneg (|v i|-|v j|))
      rw [sub_sq,sq_abs,sq_abs] at hs
      nlinarith
    _ = _ := by simp [Fin.sum_univ_three,dotProduct]; ring

lemma flatBackgroundTensor_lower {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (v : Coord3) :
    (1/2)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (flatBackgroundTensor s*ᵥv) := by
  have h := hs (v 1) (v 2)
  simp [flatBackgroundTensor,dotProduct,Matrix.mulVec,Fin.sum_univ_three] at *
  nlinarith [sq_nonneg (v 0)]

lemma flatBackgroundTensor_small_perturbation {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {H : Mat3} (hH : ‖H‖≤1/12) (v : Coord3) :
    (1/4)*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((flatBackgroundTensor s+H)*ᵥv) ∧
      v ⬝ᵥ ((flatBackgroundTensor s+H)*ᵥv)≤(3*‖flatBackgroundTensor s‖+1)*(v ⬝ᵥ v) := by
  have hv : 0≤v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hb := flatBackgroundTensor_lower hs v
  have hq := abs_le.mp (matrix_quadratic_elementwise_bound H v)
  have hf := (le_abs_self (v ⬝ᵥ (flatBackgroundTensor s*ᵥv))).trans
    (matrix_quadratic_elementwise_bound (flatBackgroundTensor s) v)
  have he : v ⬝ᵥ ((flatBackgroundTensor s+H)*ᵥv)=
      v ⬝ᵥ (flatBackgroundTensor s*ᵥv)+v ⬝ᵥ (H*ᵥv) := by rw [add_mulVec,dotProduct_add]
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hH hv
  constructor <;> nlinarith

theorem elliptic_fourier_matching {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) {δ : ℝ} (hδ : 0<δ) :
    ∃ p : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧
      ∃ (u : Coord3 → Fin 2 → ℝ) (D : Coord3 → Mat3),
        ContDiff ℝ (↑(⊤:ℕ∞)) u ∧ ContDiff ℝ (↑(⊤:ℕ∞)) D ∧
        AngularPeriodic (2*Real.pi) u ∧ AngularPeriodic (2*Real.pi) D ∧
        (∀ x,(D x).IsSymm) ∧
        (∀ x v,(1/4)*(v ⬝ᵥ v)≤v ⬝ᵥ (D x*ᵥv) ∧
          v ⬝ᵥ (D x*ᵥv)≤(3*‖flatBackgroundTensor s‖+1)*(v ⬝ᵥ v)) ∧
        (∀ j x,0<x 0 → symmetricSource D u j x=0) ∧
        (∀ x,x 0∉Icc (1/2) (11/2) → D x=flatBackgroundTensor s) ∧
        (∀ x,x 0∈Icc 0 (1/2) → u x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x,
            flatPhaseMode s ![0,k] 0 x+
              flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x]) ∧
        ∀ x,4≤x 0 → u x=![x 0,flatPhaseMode s ![0,k] 0 x] := by
  obtain ⟨f,g,hfs,hgs,hfp,hgp,hdata,hcor⟩ := smooth_fourier_matching (pa:=pa) hs hk hA hB ha hb hga hgb hra hrb hpb
  have hh := hcor (1/12) (by norm_num)
  obtain ⟨r,hr,hrb'⟩ := Metric.mem_nhds_iff.mp hh
  let p := min (r/2) (min (δ/2) (1/4))
  have hp : 0<p := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hpr : p<r := (min_le_left _ _).trans_lt (by linarith)
  have hpδ : p<δ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hp2 : p≤1/2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨H,hHs,hHp,hHt,hHsym,hHb,hHe⟩ := hrb' (by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hp] using hpr) ⟨hp,hp2⟩
  refine ⟨p,⟨hp,hp2⟩,hpδ,(fun x => fourierMatchingPair s k f g (p,x)),
    (fun x => flatBackgroundTensor s+H x),
    (fourierMatchingPair_smooth s k hfs hgs).comp (contDiff_const.prodMk contDiff_id),
    contDiff_const.add hHs,fourierMatchingPair_periodic s k hfp hgp p,?_,?_,?_,hHe,?_,?_,?_⟩
  · intro n x
    dsimp only
    rw [hHp n x]
  · intro x
    exact (flatBackgroundTensor_symm s).add (hHsym x)
  · intro x v
    exact flatBackgroundTensor_small_perturbation hs (hHb x) v
  · intro x hx
    have hz : H x=0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hHt hx'))
    dsimp only
    rw [hz,add_zero]
  · intro x hx
    have hd := hdata p ⟨hp,hp2⟩ x ⟨hx.1,by linarith [hx.2]⟩
    simp only [fourierMatchingPair,fourierMatchingCutoff_left (show x 0≤2 by linarith [hx.2]),one_mul,hd.1,hd.2]
  · intro x hx
    simp only [fourierMatchingPair,fourierMatchingCutoff_right hx,zero_mul,add_zero]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

theorem smooth_fourier_matching_with_origin {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) :
    ∃ f g : ℝ×Coord3 → ℝ,
      ContDiff ℝ (↑(⊤:ℕ∞)) f ∧ ContDiff ℝ (↑(⊤:ℕ∞)) g ∧
      (∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x))) ∧
      (∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x))) ∧
      (∀ x,f (0,x)=0) ∧ (∀ x,g (0,x)=0) ∧
      (∀ p∈Ioc 0 (1/2),∀ x : Coord3,x 0∈Icc 0 6 →
        f (p,x)=flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x ∧
        g (p,x)=flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ p in 𝓝 (0:ℝ),p∈Ioc 0 (1/2) →
        ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic (2*Real.pi) H ∧
          tsupport H⊆{x | x 0∈Icc (1/2) (11/2)} ∧ (∀ x,(H x).IsSymm) ∧
          (∀ x,‖H x‖≤ε) ∧ ∀ j x,0<x 0 →
            symmetricSource (fun y => flatBackgroundTensor s+H y) (fun y => fourierMatchingPair s k f g (p,y)) j x=0 := by
  obtain ⟨f,hfs,hfp,hfz,hfe⟩ := exists_smooth_periodic_normalized_tail
    (lam:=0) (T0:=10) (δ:=1) (R:=7) (phase:=pa) hs hga hA ha (by norm_num)
    (by simpa only [zero_add] using hra) (by norm_num)
  obtain ⟨g,hgs,hgp,hgz,hge⟩ := exists_smooth_periodic_normalized_tail
    (lam:=torusRate s ![0,k]) (T0:=10) (δ:=1) (R:=7) (phase:=pb) hs hgb hB hb (by norm_num)
    hrb (by norm_num)
  have hdata (p : ℝ) (hp : p∈Ioc 0 (1/2)) (x : Coord3) (hx : x 0∈Icc 0 6) :
      f (p,x)=flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x ∧
      g (p,x)=flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x := by
    have hx' : x 0∈Icc (-7:ℝ) 7 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    constructor
    · rw [hfe p hp x hx',flatFourier_normalized_translation]
    · rw [hge p hp x hx',flatFourier_normalized_translation]
  refine ⟨f,g,hfs,hgs,hfp,hgp,hfz 0 le_rfl,hgz 0 le_rfl,hdata,?_⟩
  intro ε hε
  have hlam := axial_torusRate_pos hs hk
  have hcor := fourierMatchingFamily_correction hs hk hfs hgs hfp hgp (hfz 0 le_rfl) (hgz 0 le_rfl) hε
  filter_upwards [hcor] with p hcor
  intro hp
  have hT : 0≤10+1/p := by have hpos := hp.1; positivity
  let aa := normalizedFourierCoefficients s 0 (10+1/p) a
  let bb := normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b
  have haa : ∀ h,|aa h|≤A := normalizedFourierCoefficients_bound ha hT
    (fun h hh => hga.le.trans (hra h hh))
  have hbb : ∀ h,|bb h|≤B := normalizedFourierCoefficients_bound hb hT
    (fun h hh => by linarith [hrb h hh])
  have hraa : ∀ h,aa h≠0 → ga≤torusRate s h := by
    intro h hh
    exact hra h (fun hz => hh ((normalizedFourierCoefficients_zero_iff _ _ _ _ _).mpr hz))
  have hrbb : ∀ h,bb h≠0 → torusRate s ![0,k]≤torusRate s h := by
    intro h hh
    have hn : b h≠0 := fun hz => hh ((normalizedFourierCoefficients_zero_iff _ _ _ _ _).mpr hz)
    linarith [hrb h hn]
  have hff (x : Coord3) (hx : x 0∈Icc 0 6) : f (p,x)=flatFourier s aa pa x := (hdata p hp x hx).1
  have hgg (x : Coord3) (hx : x 0∈Icc 0 6) : g (p,x)=flatFourier s bb pb x := (hdata p hp x hx).2
  have hm := fourierMatchingResidual_moments hs k hfs hgs hfp hgp haa hbb hpb hga hlam hraa hrbb hff hgg
  obtain ⟨H,hH,hHp,hHs,hHsy,hHr,hHb⟩ := hcor hm
  refine ⟨H,hH,hHp,hHs,hHsy,hHb,?_⟩
  exact fourierMatching_corrected_equation hs k hfs hgs haa hbb hpb hff hgg hH hHr

end ScalarConductivity

end
end

end OAI
