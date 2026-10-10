import OAI.Probability.ClassicalON.AnnulusLabels

namespace OAI

universe uι

noncomputable section
open scoped Classical
namespace ClassicalON

def coarseSite (N : ℤ) (v : Site) : Site := (v.1/N,v.2/N)
def coarseCenter (N : ℤ) (v : Site) : Site := (N*v.1,N*v.2)

theorem siteRadius_scale (N : ℤ) (hN : 0≤N) (x y : Site) :
    siteRadius (coarseCenter N x) (coarseCenter N y)=N*siteRadius x y := by
  simp only [siteRadius,coarseCenter,← mul_sub,abs_mul,abs_of_nonneg hN]
  exact (mul_max_of_nonneg _ _ hN).symm

theorem coarseSite_close (N : ℤ) (hN : 0<N) (v : Site) :
    siteRadius (coarseCenter N (coarseSite N v)) v<N := by
  change max |v.1-N*(v.1/N)| |v.2-N*(v.2/N)|<N
  rw [max_lt_iff]
  constructor
  · have he := Int.emod_add_ediv_mul v.1 N
    rw [mul_comm (v.1/N) N] at he
    have hn := Int.emod_nonneg v.1 (ne_of_gt hN)
    have hl := Int.emod_lt_of_pos v.1 hN
    rw [show v.1-N*(v.1/N)=v.1%N by omega,abs_of_nonneg hn]
    exact hl
  · have he := Int.emod_add_ediv_mul v.2 N
    rw [mul_comm (v.2/N) N] at he
    have hn := Int.emod_nonneg v.2 (ne_of_gt hN)
    have hl := Int.emod_lt_of_pos v.2 hN
    rw [show v.2-N*(v.2/N)=v.2%N by omega,abs_of_nonneg hn]
    exact hl

theorem coarse_quotient_step (N : ℤ) (hN : 0<N) (a b : ℤ) (h : |b-a|≤1) :
    |b/N-a/N|≤1 := by
  have hab := abs_le.mp h
  have h1 : b≤a+N := by omega
  have h2 : a≤b+N := by omega
  have hh1 := Int.ediv_le_ediv hN h1
  have hh2 := Int.ediv_le_ediv hN h2
  rw [Int.add_ediv_of_dvd_right (dvd_refl N),Int.ediv_self (ne_of_gt hN)] at hh1 hh2
  exact abs_le.mpr ⟨by omega,by omega⟩

theorem coarseSite_step (N : ℤ) (hN : 0<N) {x y : Site} (h : siteRadius x y≤1) :
    siteRadius (coarseSite N x) (coarseSite N y)≤1 := by
  have hh := siteRadius_le_iff x y 1 |>.mp h
  exact max_le (coarse_quotient_step N hN _ _ hh.1) (coarse_quotient_step N hN _ _ hh.2)

theorem coarseSite_distance (N : ℤ) (hN : 0<N) (x y : Site) :
    siteRadius x y≤N*(siteRadius (coarseSite N x) (coarseSite N y)+2) := by
  have h1 := coarseSite_close N hN x
  have h2 := coarseSite_close N hN y
  have h3 := siteRadius_triangle x (coarseCenter N (coarseSite N x)) y
  have h4 := siteRadius_triangle (coarseCenter N (coarseSite N x)) (coarseCenter N (coarseSite N y)) y
  rw [siteRadius_scale N (le_of_lt hN)] at h4
  rw [siteRadius_symm x (coarseCenter N (coarseSite N x))] at h3
  nlinarith

abbrev SiteColor := Fin 5 × Fin 5

def siteColor (v : Site) : SiteColor :=
  (⟨(v.1%5).toNat,by omega⟩,⟨(v.2%5).toNat,by omega⟩)

theorem sameColor_far {x y : Site} (hxy : x≠y) (h : siteColor x=siteColor y) :
    4<siteRadius x y := by
  have h1 := congrArg (fun c : SiteColor => c.1.val) h
  have h2 := congrArg (fun c : SiteColor => c.2.val) h
  change (x.1%5).toNat=(y.1%5).toNat at h1
  change (x.2%5).toNat=(y.2%5).toNat at h2
  by_contra hn
  have hr : |y.1-x.1|≤4 ∧ |y.2-x.2|≤4 := (siteRadius_le_iff x y 4).mp (by omega)
  have ha := abs_le.mp hr.1
  have hb := abs_le.mp hr.2
  apply hxy
  apply Prod.ext <;> omega

theorem sameColor_separated {ι : Type uι} (N : ℤ) (hN : 0<N) (v : ι → Site)
    (hv : Function.Injective v) (c : SiteColor) :
    SeparatedCenters N (fun i : {i // siteColor (v i)=c} => coarseCenter N (v i.val)) := by
  intro i j hij
  rw [siteRadius_scale N (le_of_lt hN)]
  have hd : v i.val≠v j.val := fun h => hij (Subtype.ext (hv h))
  have hh := sameColor_far hd (i.property.trans j.property.symm)
  nlinarith

end ClassicalON

end

end OAI
