import Mathlib
import OAI.Combinatorics.StripMass.Basic

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram

theorem eighthRoot_power {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) (k : ℕ) :
    q^k = (-1)^(k/8) * q^(k%8) := by
  calc
    q^k = q^(8*(k/8)+k%8) := congrArg (q^·) (by omega)
    _ = (q^8)^(k/8) * q^(k%8) := by rw [pow_add, pow_mul]
    _ = _ := by rw [h]

theorem eighthRoot_power_8 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^8 = -(1) := by
  have ht := eighthRoot_power h 8
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_9 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^9 = -(q^1) := by
  have ht := eighthRoot_power h 9
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_10 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^10 = -(q^2) := by
  have ht := eighthRoot_power h 10
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_11 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^11 = -(q^3) := by
  have ht := eighthRoot_power h 11
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_12 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^12 = -(q^4) := by
  have ht := eighthRoot_power h 12
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_13 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^13 = -(q^5) := by
  have ht := eighthRoot_power h 13
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_14 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^14 = -(q^6) := by
  have ht := eighthRoot_power h 14
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_15 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^15 = -(q^7) := by
  have ht := eighthRoot_power h 15
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_16 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^16 = (1) := by
  have ht := eighthRoot_power h 16
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_17 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^17 = (q^1) := by
  have ht := eighthRoot_power h 17
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_18 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^18 = (q^2) := by
  have ht := eighthRoot_power h 18
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_19 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^19 = (q^3) := by
  have ht := eighthRoot_power h 19
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_20 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^20 = (q^4) := by
  have ht := eighthRoot_power h 20
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_21 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^21 = (q^5) := by
  have ht := eighthRoot_power h 21
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_22 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^22 = (q^6) := by
  have ht := eighthRoot_power h 22
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_23 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^23 = (q^7) := by
  have ht := eighthRoot_power h 23
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_24 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^24 = -(1) := by
  have ht := eighthRoot_power h 24
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_25 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^25 = -(q^1) := by
  have ht := eighthRoot_power h 25
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_26 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^26 = -(q^2) := by
  have ht := eighthRoot_power h 26
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_27 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^27 = -(q^3) := by
  have ht := eighthRoot_power h 27
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_28 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^28 = -(q^4) := by
  have ht := eighthRoot_power h 28
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_29 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^29 = -(q^5) := by
  have ht := eighthRoot_power h 29
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_30 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^30 = -(q^6) := by
  have ht := eighthRoot_power h 30
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_31 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^31 = -(q^7) := by
  have ht := eighthRoot_power h 31
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_32 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^32 = (1) := by
  have ht := eighthRoot_power h 32
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_33 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^33 = (q^1) := by
  have ht := eighthRoot_power h 33
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_34 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^34 = (q^2) := by
  have ht := eighthRoot_power h 34
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_35 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^35 = (q^3) := by
  have ht := eighthRoot_power h 35
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_36 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^36 = (q^4) := by
  have ht := eighthRoot_power h 36
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_37 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^37 = (q^5) := by
  have ht := eighthRoot_power h 37
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_38 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^38 = (q^6) := by
  have ht := eighthRoot_power h 38
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_39 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^39 = (q^7) := by
  have ht := eighthRoot_power h 39
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_40 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^40 = -(1) := by
  have ht := eighthRoot_power h 40
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_41 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^41 = -(q^1) := by
  have ht := eighthRoot_power h 41
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_42 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^42 = -(q^2) := by
  have ht := eighthRoot_power h 42
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_43 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^43 = -(q^3) := by
  have ht := eighthRoot_power h 43
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_44 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^44 = -(q^4) := by
  have ht := eighthRoot_power h 44
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_45 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^45 = -(q^5) := by
  have ht := eighthRoot_power h 45
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_46 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^46 = -(q^6) := by
  have ht := eighthRoot_power h 46
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_47 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^47 = -(q^7) := by
  have ht := eighthRoot_power h 47
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_48 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^48 = (1) := by
  have ht := eighthRoot_power h 48
  norm_num at ht
  simpa only [pow_one] using ht


 

 


theorem eighthRoot_power_49 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^49 = (q^1) := by
  have ht := eighthRoot_power h 49
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_50 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^50 = (q^2) := by
  have ht := eighthRoot_power h 50
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_51 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^51 = (q^3) := by
  have ht := eighthRoot_power h 51
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_52 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^52 = (q^4) := by
  have ht := eighthRoot_power h 52
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_53 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^53 = (q^5) := by
  have ht := eighthRoot_power h 53
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_54 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^54 = (q^6) := by
  have ht := eighthRoot_power h 54
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_55 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^55 = (q^7) := by
  have ht := eighthRoot_power h 55
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_56 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^56 = -(1) := by
  have ht := eighthRoot_power h 56
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_57 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^57 = -(q^1) := by
  have ht := eighthRoot_power h 57
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_58 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^58 = -(q^2) := by
  have ht := eighthRoot_power h 58
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_59 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^59 = -(q^3) := by
  have ht := eighthRoot_power h 59
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_60 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^60 = -(q^4) := by
  have ht := eighthRoot_power h 60
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_61 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^61 = -(q^5) := by
  have ht := eighthRoot_power h 61
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_62 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^62 = -(q^6) := by
  have ht := eighthRoot_power h 62
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_63 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^63 = -(q^7) := by
  have ht := eighthRoot_power h 63
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_64 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^64 = (1) := by
  have ht := eighthRoot_power h 64
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_65 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^65 = (q^1) := by
  have ht := eighthRoot_power h 65
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_66 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^66 = (q^2) := by
  have ht := eighthRoot_power h 66
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_67 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^67 = (q^3) := by
  have ht := eighthRoot_power h 67
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_68 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^68 = (q^4) := by
  have ht := eighthRoot_power h 68
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_69 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^69 = (q^5) := by
  have ht := eighthRoot_power h 69
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_70 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^70 = (q^6) := by
  have ht := eighthRoot_power h 70
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_71 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^71 = (q^7) := by
  have ht := eighthRoot_power h 71
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_72 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^72 = -(1) := by
  have ht := eighthRoot_power h 72
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_73 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^73 = -(q^1) := by
  have ht := eighthRoot_power h 73
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_74 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^74 = -(q^2) := by
  have ht := eighthRoot_power h 74
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_75 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^75 = -(q^3) := by
  have ht := eighthRoot_power h 75
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_76 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^76 = -(q^4) := by
  have ht := eighthRoot_power h 76
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_77 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^77 = -(q^5) := by
  have ht := eighthRoot_power h 77
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_78 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^78 = -(q^6) := by
  have ht := eighthRoot_power h 78
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_79 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^79 = -(q^7) := by
  have ht := eighthRoot_power h 79
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_80 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^80 = (1) := by
  have ht := eighthRoot_power h 80
  norm_num at ht
  simpa only [pow_one] using ht

end CriticalStrip.Diagram

end OAI
