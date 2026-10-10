import OAI.Analysis.Triangular.Signs.SineGridDefs

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma unit_grid_cover {x : ℝ} (hx : x∈Icc 0 1) :
    ∃ k : Fin 100, (k.val:ℝ)/100≤x ∧ x≤(k.val+1:ℝ)/100 := by
  by_cases he : x=1
  · subst x
    exact ⟨99,by norm_num,by norm_num⟩
  · have hx1 : x<1 := lt_of_le_of_ne hx.2 he
    let n : ℕ := ⌊100*x⌋₊
    have hn1 : (n:ℝ)≤100*x := Nat.floor_le (by nlinarith [hx.1])
    have hn2 : 100*x<(n:ℝ)+1 := Nat.lt_floor_add_one _
    have hn : n<100 := by
      by_contra! hh
      have : (100:ℝ)≤n := by exact_mod_cast hh
      nlinarith
    exact ⟨⟨n,hn⟩,by dsimp; linarith,by dsimp; linarith⟩
lemma cell_displacement (u : Fin 30) (k : Fin 100) {x : ℝ}
    (hx : (k.val:ℝ)/100≤x ∧ x≤(k.val+1:ℝ)/100) :
    (localHalf u:ℝ)*x∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ) := by
  have hlo : (cellLo u k:ℝ)=min ((localHalf u:ℝ)*k.val/100) ((localHalf u:ℝ)*(k.val+1)/100) := by
    unfold cellLo; push_cast; rfl
  have hhi : (cellHi u k:ℝ)=max ((localHalf u:ℝ)*k.val/100) ((localHalf u:ℝ)*(k.val+1)/100) := by
    unfold cellHi; push_cast; rfl
  rw [hlo,hhi]
  by_cases h : 0≤(localHalf u:ℝ)
  · have hab : (localHalf u:ℝ)*k.val/100≤(localHalf u:ℝ)*(k.val+1)/100 := by nlinarith
    rw [min_eq_left hab,max_eq_right hab]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 h,mul_le_mul_of_nonneg_left hx.2 h]
  · have h := le_of_not_ge h
    have hab : (localHalf u:ℝ)*(k.val+1)/100≤(localHalf u:ℝ)*k.val/100 := by nlinarith
    rw [min_eq_right hab,max_eq_left hab]
    constructor <;> nlinarith [mul_le_mul_of_nonpos_left hx.1 h,mul_le_mul_of_nonpos_left hx.2 h]
def localBoundary (n : ℕ) : ℚ :=
  if hn : n<31 then ![-5/2,0,1/2,1,2,3,7/2,4,11/2,7,8,9,21/2,12,25/2,13,29/2,16,35/2,19,20,21,23,25,26,27,55/2,28,59/2,31,67/2] ⟨n,hn⟩ else 0
lemma local_boundary_end : localBoundary 0= -5/2 ∧ localBoundary 30=67/2 := by decide +kernel
lemma local_boundary_geometry (u : Fin 30) :
    min (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary u.val ∧
    max (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary (u.val+1) ∧
    localHalf u≠0 ∧ 0≤localCenter u ∧ localCenter u%36∈residues ∧
    (localCenter u<25 → localBoundary (u.val+1)≤23) ∧
    (u.val<16 → localBoundary (u.val+1)≤29/2) ∧
    (21<u.val → 23≤localBoundary u.val) := by
  exact (show ∀ u : Fin 30,
    min (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary u.val ∧
    max (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary (u.val+1) ∧
    localHalf u≠0 ∧ 0≤localCenter u ∧ localCenter u%36∈residues ∧
    (localCenter u<25 → localBoundary (u.val+1)≤23) ∧
    (u.val<16 → localBoundary (u.val+1)≤29/2) ∧
    (21<u.val → 23≤localBoundary u.val) by decide +kernel) u
lemma local_halfGap_cover {t : ℝ} (ht : t∈Ico (-(5/2)) (67/2)) :
    ∃ u : Fin 30,∃ x∈Icc (0:ℝ) 1,t=(localCenter u:ℝ)+(localHalf u:ℝ)*x ∧
      t∈Ico (localBoundary u.val:ℝ) (localBoundary (u.val+1):ℝ) := by
  have hex : ∃ n : ℕ,1≤n ∧ n≤30 ∧ t<(localBoundary n:ℝ) := by
    refine ⟨30,by omega,le_rfl,?_⟩
    simpa only [local_boundary_end.2,Rat.cast_div,Rat.cast_ofNat] using ht.2
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  change 1≤n ∧ n≤30 ∧ t<(localBoundary n:ℝ) at hn
  have hl : (localBoundary (n-1):ℝ)≤t := by
    by_cases h : n=1
    · simp only [h,Nat.sub_self,local_boundary_end.1,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat]
      linarith [ht.1]
    · have hmin := Nat.find_min hex (show n-1<n by omega)
      by_contra! hh
      exact hmin ⟨by omega,by omega,hh⟩
  let u : Fin 30 := ⟨n-1,by omega⟩
  have hg := local_boundary_geometry u
  have hg₁ : min (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ))=(localBoundary u.val:ℝ) := by
    simpa only [Rat.cast_min,Rat.cast_add,Rat.cast_intCast] using congrArg (fun q : ℚ => (q:ℝ)) hg.1
  have hg₂ : max (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ))=(localBoundary (u.val+1):ℝ) := by
    simpa only [Rat.cast_max,Rat.cast_add,Rat.cast_intCast] using congrArg (fun q : ℚ => (q:ℝ)) hg.2.1
  have hu : t<(localBoundary (u.val+1):ℝ) := by simpa only [u,show n-1+1=n by omega] using hn.2.2
  have hb : t∈uIcc (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ)) := by
    rw [uIcc,mem_Icc,hg₁,hg₂]
    exact ⟨hl,hu.le⟩
  have hne : (localHalf u:ℝ)≠0 := by exact_mod_cast hg.2.2.1
  refine ⟨u,(t-localCenter u)/(localHalf u:ℝ),?_,?_,hl,hu⟩
  · by_cases hp : 0<(localHalf u:ℝ)
    · rw [uIcc_of_le (by linarith)] at hb
      exact ⟨div_nonneg (sub_nonneg.mpr hb.1) hp.le,(div_le_one hp).mpr (by linarith [hb.2])⟩
    · have hp : (localHalf u:ℝ)<0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      rw [uIcc_of_ge (by linarith)] at hb
      exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hb.2) hp.le,(div_le_one_of_neg hp).mpr (by linarith [hb.1])⟩
  · field_simp
    ring
end AtomicTriangular.Construction
end

end OAI
