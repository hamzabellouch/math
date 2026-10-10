import OAI.MathematicalPhysics.Transonic.Certificates.Jet08
import OAI.MathematicalPhysics.Transonic.Exterior.Weight

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C08
open SepticProfile.ExteriorJet SepticProfile.ExteriorJet.NormalizedTrace SepticProfile.FixedInterval SepticProfile.ShootingParameters
def lo : ℝ := -5648119/8000000
def hi : ℝ := -45184919/64000000
theorem qpos : 0<Q := by decide +kernel
theorem lo_mem : lo∈Set.Icc leftEnd rightEnd := by norm_num [lo,leftEnd,rightEnd]
theorem hi_mem : hi∈Set.Icc leftEnd rightEnd := by norm_num [hi,leftEnd,rightEnd]
theorem sig_lo : Holds Q sig (sigma lo) := by norm_num [Holds,Q,sig,lo,ShootingParameters.sigma,d,e,a,k]
theorem sig_hi : Holds Q sig (sigma hi) := by norm_num [Holds,Q,sig,hi,ShootingParameters.sigma,d,e,a,k]
theorem sig_mem {t:ℝ} (ht : t∈Set.Icc lo hi) : Holds Q sig (sigma t) := by
  have ht0 : t∈Set.Icc leftEnd rightEnd := ⟨le_trans lo_mem.1 ht.1,le_trans ht.2 hi_mem.2⟩
  exact holds_between qpos sig_lo sig_hi ⟨sigma_monotone lo_mem ht0 ht.1,sigma_monotone ht0 hi_mem ht.2⟩
theorem kap_lo : Holds Q kap (kappa lo) := by norm_num [Holds,Q,kap,lo,ShootingParameters.kappa,d,e,a,k]
theorem kap_hi : Holds Q kap (kappa hi) := by norm_num [Holds,Q,kap,hi,ShootingParameters.kappa,d,e,a,k]
theorem kap_mem {t:ℝ} (ht : t∈Set.Icc lo hi) : Holds Q kap (kappa t) := by
  have ht0 : t∈Set.Icc leftEnd rightEnd := ⟨le_trans lo_mem.1 ht.1,le_trans ht.2 hi_mem.2⟩
  exact holds_between qpos kap_hi kap_lo ⟨kappa_antitone ht0 hi_mem ht.2,kappa_antitone lo_mem ht0 ht.1⟩
theorem s_lo : Holds Q s (slope lo) := by norm_num [Holds,Q,s,lo,ShootingParameters.slope,d,e,a,k]
theorem s_hi : Holds Q s (slope hi) := by norm_num [Holds,Q,s,hi,ShootingParameters.slope,d,e,a,k]
theorem s_mem {t:ℝ} (ht : t∈Set.Icc lo hi) : Holds Q s (slope t) := by
  have ht0 : t∈Set.Icc leftEnd rightEnd := ⟨le_trans lo_mem.1 ht.1,le_trans ht.2 hi_mem.2⟩
  exact holds_between qpos s_hi s_lo ⟨slope_antitone ht0 hi_mem ht.2,slope_antitone lo_mem ht0 ht.1⟩
theorem rho_lo : Holds Q rho (ratio lo) := by norm_num [Holds,Q,rho,lo,ShootingParameters.ratio,d,e,a,k]
theorem rho_hi : Holds Q rho (ratio hi) := by norm_num [Holds,Q,rho,hi,ShootingParameters.ratio,d,e,a,k]
theorem rho_mem {t:ℝ} (ht : t∈Set.Icc lo hi) : Holds Q rho (ratio t) := by
  have ht0 : t∈Set.Icc leftEnd rightEnd := ⟨le_trans lo_mem.1 ht.1,le_trans ht.2 hi_mem.2⟩
  exact holds_between qpos rho_lo rho_hi ⟨ratio_monotone lo_mem ht0 ht.1,ratio_monotone ht0 hi_mem ht.2⟩
theorem weights_eq : weights=sourceWeights Q sig kap := by rfl
theorem st_eq : st=scale 1 256 s := by decide +kernel
theorem L0_eq : L0=sourceL0 Q sig st := by decide +kernel
theorem b1_eq : trace.b 1=st := by decide +kernel
theorem den2 : trace.den 2=sourceDen Q L0 rho 2 := by decide +kernel
theorem den3 : trace.den 3=sourceDen Q L0 rho 3 := by decide +kernel
theorem den4 : trace.den 4=sourceDen Q L0 rho 4 := by decide +kernel
theorem den5 : trace.den 5=sourceDen Q L0 rho 5 := by decide +kernel
theorem den6 : trace.den 6=sourceDen Q L0 rho 6 := by decide +kernel
theorem den7 : trace.den 7=sourceDen Q L0 rho 7 := by decide +kernel
theorem den8 : trace.den 8=sourceDen Q L0 rho 8 := by decide +kernel
theorem den9 : trace.den 9=sourceDen Q L0 rho 9 := by decide +kernel
theorem den10 : trace.den 10=sourceDen Q L0 rho 10 := by decide +kernel
theorem den11 : trace.den 11=sourceDen Q L0 rho 11 := by decide +kernel
theorem den12 : trace.den 12=sourceDen Q L0 rho 12 := by decide +kernel
theorem den13 : trace.den 13=sourceDen Q L0 rho 13 := by decide +kernel
theorem den14 : trace.den 14=sourceDen Q L0 rho 14 := by decide +kernel
theorem den15 : trace.den 15=sourceDen Q L0 rho 15 := by decide +kernel
theorem den16 : trace.den 16=sourceDen Q L0 rho 16 := by decide +kernel
theorem den17 : trace.den 17=sourceDen Q L0 rho 17 := by decide +kernel
theorem den18 : trace.den 18=sourceDen Q L0 rho 18 := by decide +kernel
theorem den19 : trace.den 19=sourceDen Q L0 rho 19 := by decide +kernel
theorem den20 : trace.den 20=sourceDen Q L0 rho 20 := by decide +kernel
theorem den21 : trace.den 21=sourceDen Q L0 rho 21 := by decide +kernel
theorem den22 : trace.den 22=sourceDen Q L0 rho 22 := by decide +kernel
theorem den23 : trace.den 23=sourceDen Q L0 rho 23 := by decide +kernel
theorem den24 : trace.den 24=sourceDen Q L0 rho 24 := by decide +kernel
theorem den25 : trace.den 25=sourceDen Q L0 rho 25 := by decide +kernel
theorem den26 : trace.den 26=sourceDen Q L0 rho 26 := by decide +kernel
theorem den27 : trace.den 27=sourceDen Q L0 rho 27 := by decide +kernel
theorem den28 : trace.den 28=sourceDen Q L0 rho 28 := by decide +kernel
theorem den29 : trace.den 29=sourceDen Q L0 rho 29 := by decide +kernel
theorem den30 : trace.den 30=sourceDen Q L0 rho 30 := by decide +kernel
theorem den31 : trace.den 31=sourceDen Q L0 rho 31 := by decide +kernel
theorem den32 : trace.den 32=sourceDen Q L0 rho 32 := by decide +kernel
theorem den33 : trace.den 33=sourceDen Q L0 rho 33 := by decide +kernel
theorem den34 : trace.den 34=sourceDen Q L0 rho 34 := by decide +kernel
theorem den35 : trace.den 35=sourceDen Q L0 rho 35 := by decide +kernel
theorem den36 : trace.den 36=sourceDen Q L0 rho 36 := by decide +kernel
theorem den37 : trace.den 37=sourceDen Q L0 rho 37 := by decide +kernel
theorem den38 : trace.den 38=sourceDen Q L0 rho 38 := by decide +kernel
theorem den39 : trace.den 39=sourceDen Q L0 rho 39 := by decide +kernel
theorem den40 : trace.den 40=sourceDen Q L0 rho 40 := by decide +kernel
theorem den41 : trace.den 41=sourceDen Q L0 rho 41 := by decide +kernel
theorem den42 : trace.den 42=sourceDen Q L0 rho 42 := by decide +kernel
theorem den43 : trace.den 43=sourceDen Q L0 rho 43 := by decide +kernel
theorem den44 : trace.den 44=sourceDen Q L0 rho 44 := by decide +kernel
theorem den45 : trace.den 45=sourceDen Q L0 rho 45 := by decide +kernel
theorem den46 : trace.den 46=sourceDen Q L0 rho 46 := by decide +kernel
theorem den47 : trace.den 47=sourceDen Q L0 rho 47 := by decide +kernel
theorem den48 : trace.den 48=sourceDen Q L0 rho 48 := by decide +kernel
theorem den49 : trace.den 49=sourceDen Q L0 rho 49 := by decide +kernel
theorem den50 : trace.den 50=sourceDen Q L0 rho 50 := by decide +kernel
theorem den51 : trace.den 51=sourceDen Q L0 rho 51 := by decide +kernel
theorem den52 : trace.den 52=sourceDen Q L0 rho 52 := by decide +kernel
theorem den53 : trace.den 53=sourceDen Q L0 rho 53 := by decide +kernel
theorem den54 : trace.den 54=sourceDen Q L0 rho 54 := by decide +kernel
theorem den55 : trace.den 55=sourceDen Q L0 rho 55 := by decide +kernel
theorem den56 : trace.den 56=sourceDen Q L0 rho 56 := by decide +kernel
theorem den57 : trace.den 57=sourceDen Q L0 rho 57 := by decide +kernel
theorem den58 : trace.den 58=sourceDen Q L0 rho 58 := by decide +kernel
theorem den59 : trace.den 59=sourceDen Q L0 rho 59 := by decide +kernel
theorem den60 : trace.den 60=sourceDen Q L0 rho 60 := by decide +kernel
theorem den61 : trace.den 61=sourceDen Q L0 rho 61 := by decide +kernel
theorem den62 : trace.den 62=sourceDen Q L0 rho 62 := by decide +kernel
theorem den63 : trace.den 63=sourceDen Q L0 rho 63 := by decide +kernel
theorem den64 : trace.den 64=sourceDen Q L0 rho 64 := by decide +kernel
theorem den65 : trace.den 65=sourceDen Q L0 rho 65 := by decide +kernel
theorem den66 : trace.den 66=sourceDen Q L0 rho 66 := by decide +kernel
theorem den67 : trace.den 67=sourceDen Q L0 rho 67 := by decide +kernel
theorem den68 : trace.den 68=sourceDen Q L0 rho 68 := by decide +kernel
theorem den69 : trace.den 69=sourceDen Q L0 rho 69 := by decide +kernel
theorem den70 : trace.den 70=sourceDen Q L0 rho 70 := by decide +kernel
theorem den71 : trace.den 71=sourceDen Q L0 rho 71 := by decide +kernel
theorem den72 : trace.den 72=sourceDen Q L0 rho 72 := by decide +kernel
theorem den73 : trace.den 73=sourceDen Q L0 rho 73 := by decide +kernel
theorem den74 : trace.den 74=sourceDen Q L0 rho 74 := by decide +kernel
theorem den_eq (n:ℕ) (hn:2≤n) (hn1:n≤74) : trace.den n=sourceDen Q L0 rho n := by
  interval_cases n
  · exact den2
  · exact den3
  · exact den4
  · exact den5
  · exact den6
  · exact den7
  · exact den8
  · exact den9
  · exact den10
  · exact den11
  · exact den12
  · exact den13
  · exact den14
  · exact den15
  · exact den16
  · exact den17
  · exact den18
  · exact den19
  · exact den20
  · exact den21
  · exact den22
  · exact den23
  · exact den24
  · exact den25
  · exact den26
  · exact den27
  · exact den28
  · exact den29
  · exact den30
  · exact den31
  · exact den32
  · exact den33
  · exact den34
  · exact den35
  · exact den36
  · exact den37
  · exact den38
  · exact den39
  · exact den40
  · exact den41
  · exact den42
  · exact den43
  · exact den44
  · exact den45
  · exact den46
  · exact den47
  · exact den48
  · exact den49
  · exact den50
  · exact den51
  · exact den52
  · exact den53
  · exact den54
  · exact den55
  · exact den56
  · exact den57
  · exact den58
  · exact den59
  · exact den60
  · exact den61
  · exact den62
  · exact den63
  · exact den64
  · exact den65
  · exact den66
  · exact den67
  · exact den68
  · exact den69
  · exact den70
  · exact den71
  · exact den72
  · exact den73
  · exact den74
theorem num74_pos : 0<(trace.num 74).center-(trace.num 74).radius := by decide +kernel
end SepticProfile.ExteriorCertificates.C08

end
end

end OAI
