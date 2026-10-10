import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowConjugation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointMultiplicity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSpectralDisk
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileExistence

namespace OAI

/-! The free matching condition forces the phase, translation and scaling
zeros at 0, 1/2 and 1. These identities use the actual H columns. -/

namespace DefocusingNLS
open ProfileCertificate

private theorem stationary_column_shifts (q s : ℂ) (hq : q.re=0) (hq0 : q≠0)
    (hs : s.re=0) (hs0 : s≠0) (hd : slowBoundaryColumn q 6 s 1=0) :
    slowBoundaryColumn (q+1) 7 s 0=0 ∧
      slowBoundaryColumn (q+1) 6 s 1 = -slowBoundaryColumn (q+1) 6 s 0 := by
  have hH : regularizedSlowSolution (q+1) 7 (-s)=0 := by
    change q*regularizedSlowSolution (q+1) 7 (-s)=0 at hd
    exact (mul_eq_zero.mp hd).resolve_left hq0
  refine ⟨hH,?_⟩
  have ha := regularizedSlowSolution_adjacent (q+1) 6 (-s)
    (by simp [hq]) (by simp [hs]) (neg_ne_zero.mpr hs0)
  rw [hH] at ha
  change (q+1)*regularizedSlowSolution (q+1+1) 7 (-s) =
    -regularizedSlowSolution (q+1) 6 (-s)
  linear_combination -ha

private theorem stationary_column_pair_zeros (q s : ℂ) (hq : q.re=0) (hq0 : q≠0)
    (hs : s.re=0) (hs0 : s≠0) (hd : slowBoundaryColumn q 6 s 1=0) :
    matchingColumnDeterminant (slowBoundaryColumn q 6 s)
      (slowBoundaryColumn (star q) 6 (star s))=0 ∧
    matchingColumnDeterminant (slowBoundaryColumn (q+1) 7 s)
      (slowBoundaryColumn (star q+1) 7 (star s))=0 ∧
    matchingColumnDeterminant (slowBoundaryColumn (q+1) 6 s)
      (slowBoundaryColumn (star q+1) 6 (star s))=0 := by
  have hsim : s.im≠0 := by
    intro hi
    exact hs0 (Complex.ext hs hi)
  have hslit : -s∈Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hsim))
  have hstar := congrFun (slowBoundaryColumn_star q 6 s hslit) 1
  change star (slowBoundaryColumn q 6 s 1) = slowBoundaryColumn (star q) 6 (star s) 1 at hstar
  rw [hd,star_zero] at hstar
  have hqm : (star q).re=0 := by simpa only [Complex.star_def,Complex.conj_re] using hq
  have hsm : (star s).re=0 := by simpa only [Complex.star_def,Complex.conj_re] using hs
  have hp := stationary_column_shifts q s hq hq0 hs hs0 hd
  have hm := stationary_column_shifts (star q) (star s) hqm
    (star_ne_zero.mpr hq0) hsm (star_ne_zero.mpr hs0) hstar.symm
  refine ⟨?_,?_,?_⟩
  · simp only [matchingColumnDeterminant,hd,hstar.symm,mul_zero,zero_mul,sub_self]
  · simp only [matchingColumnDeterminant,hp.1,hm.1,zero_mul,mul_zero,sub_self]
  · rw [matchingColumnDeterminant,hp.2,hm.2]
    ring

theorem free_spectral_symmetry_zeros (b Z : ℝ) (hb : b≠0) (hZ : Z≠0)
    (hd : deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)
      (-Complex.I*(Z : ℂ))=0) :
    spectralSlowDeterminant 0 b Z 0=0 ∧
      spectralSlowDeterminant 1 b Z (1/2)=0 ∧
      spectralSlowDeterminant 0 b Z 1=0 := by
  let q := -Complex.I*(b : ℂ)
  let s := Complex.I*(Z : ℂ)
  have hq : q.re=0 := by simp [q]
  have hs : s.re=0 := by simp [s]
  have hq0 : q≠0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast hb)
  have hs0 : s≠0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hZ)
  have hsim : s.im≠0 := by simpa [s] using hZ
  have hcol : slowBoundaryColumn q 6 s 1=0 := by
    rw [slowBoundaryColumn_eq_jet q 6 s (by simp [hq]) hs hsim]
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,neg_mul,neg_zero,q,s] using congrArg Neg.neg hd
  have hz := stationary_column_pair_zeros q s hq hq0 hs hs0 hcol
  have hqm : star q=Complex.I*(b : ℂ) := by
    simp only [q,star_mul,star_neg,Complex.star_def,Complex.conj_I,Complex.conj_ofReal,neg_neg]
    ring
  have hsm : star s= -Complex.I*(Z : ℂ) := by
    simp only [s,star_mul,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
    ring
  have hq0p : spectralQ 0 1 b 0=q := by simp [spectralQ,q]
  have hq0m : spectralQ 0 (-1) b 0=star q := by rw [hqm]; simp [spectralQ]
  have hqtp : spectralQ 1 1 b (1/2)=q+1 := by simp [spectralQ,q]; ring
  have hqtm : spectralQ 1 (-1) b (1/2)=star q+1 := by rw [hqm]; simp [spectralQ]; ring
  have hqsp : spectralQ 0 1 b 1=q+1 := by simp [spectralQ,q]; ring
  have hqsm : spectralQ 0 (-1) b 1=star q+1 := by rw [hqm]; simp [spectralQ]; ring
  simpa only [spectralSlowDeterminant,hq0p,hq0m,hqtp,hqtm,hqsp,hqsm,
    hsm,s,Nat.reduceAdd,neg_mul] using hz

theorem radialShooting_stationary_of_matching (w : RadialShootingDisk)
    (hw : diskProfile w=0) :
    deriv (regularizedSlowSolution (-Complex.I*(radialShootingB w : ℂ)) 6)
      (-Complex.I*(radialShootingZ w : ℂ))=0 := by
  obtain ⟨hb,hz⟩ := disk_coordinates w
  have hZ : 0<radialShootingZ w := by
    have hh := (abs_le.mp hz).1
    norm_num [radius,centerZ] at hh
    dsimp only [radialShootingZ]
    norm_num [centerZ]
    linarith
  have hn : regularizedSlowSolution (-Complex.I*(radialShootingB w : ℂ)) 6
      (-Complex.I*(radialShootingZ w : ℂ))≠0 := by
    simpa only [radialShootingB,radialShootingZ,neg_mul] using
      free_profile_nonzero w.val.re w.val.im hb hz
  change freeProfileJ (radialShootingB w) (radialShootingZ w)=0 at hw
  rw [freeProfileJ_eq_log_derivative _ _ hZ] at hw
  exact neg_eq_zero.mp ((div_eq_zero_iff.mp hw).resolve_right hn)

theorem radialFree_spectral_symmetry_zeros (w : RadialShootingDisk)
    (hw : diskProfile w=0) :
    spectralSlowDeterminant 0 (radialShootingB w) ((radialShootingR w)^2/4) 0=0 ∧
      spectralSlowDeterminant 1 (radialShootingB w) ((radialShootingR w)^2/4) (1/2)=0 ∧
      spectralSlowDeterminant 0 (radialShootingB w) ((radialShootingR w)^2/4) 1=0 := by
  rw [radialShootingR_sq]
  have hb : radialShootingB w≠0 := by
    have hh := (radialShooting_geometry w).1.1
    linarith
  have hZ : radialShootingZ w≠0 := by
    have hR := (radialShooting_geometry w).2.1
    have hh := radialShootingR_sq w
    intro hz
    rw [hz] at hh
    nlinarith [sq_nonneg (radialShootingR w)]
  exact free_spectral_symmetry_zeros _ _ hb hZ (radialShooting_stationary_of_matching w hw)

end DefocusingNLS

end OAI
