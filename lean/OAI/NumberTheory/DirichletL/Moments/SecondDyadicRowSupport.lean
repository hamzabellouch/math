import OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicRowSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
local notation "O"=>HeckeFamily.O

 def dyadicRows (rows:Finset O) (n:Fin 4→ℤ):Finset O:=
  rows.filter (fun z=>dyadicWeight (n 1) (normValue z)≠0)

 theorem mem_dyadicRows (rows:Finset O)(n:Fin 4→ℤ)(z:O):
    z∈dyadicRows rows n ↔ z∈rows ∧ dyadicWeight (n 1) (normValue z)≠0:=
  Finset.mem_filter

 theorem dyadicRows_subset (rows:Finset O)(n:Fin 4→ℤ):dyadicRows rows n⊆rows:=
  Finset.filter_subset _ _

 theorem dyadicRows_norm (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):
    dyadicScale (n 1)/4<normValue z ∧ normValue z<dyadicScale (n 1):=
  dyadicWeight_support (n 1) ((mem_dyadicRows rows n z).mp hz).2

 theorem dyadicRows_nonzero (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):z≠0:=by
  have hn:0<normValue z:=(div_pos (dyadicScale_pos (n 1)) (by norm_num)).trans
    (dyadicRows_norm rows n z hz).1
  intro he
  simp only [he,normValue_eq_embedding,map_zero,norm_zero,zero_pow (by decide : 2≠0)] at hn
  exact (lt_irrefl 0) hn

 theorem dyadicRows_power_cap (rows:Finset O)(n:Fin 4→ℤ)(Z:ℝ)(hZ:1<Z)
    (z:O)(hz:z∈dyadicRows rows n):
    (Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^(Real.logb Z (dyadicScale (n 1))):=by
  rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (dyadicScale_pos (n 1))]
  exact (dyadicRows_norm rows n z hz).2.le

 theorem physicalBlock_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows rows n) W K n:=by
  unfold physicalBlock dyadicRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hd:dyadicWeight (n 1) (normValue z)=0
  · simp only [hd,ne_eq,not_true_eq_false,mul_zero,zero_mul,
      Complex.ofReal_zero,Finset.sum_const_zero,ite_self]
  · simp only [hd,ne_eq,not_false_eq_true,ite_true]

 theorem dyadicRows_liveRows (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)
    (rows:Finset O)(n:Fin 4→ℤ):
    dyadicRows (liveRows C D U R rows) n=liveRows C D U R (dyadicRows rows n):=by
  ext z
  simp only [dyadicRows,liveRows,Finset.mem_filter]
  tauto

 theorem physicalBlock_live_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows (liveRows C D U R rows) n) W K n:=
  (physicalBlock_live_rows η t S β C D hC hD U R rows W K n).trans
    (physicalBlock_dyadic_rows η t S β C D hC hD U R _ W K n)

end SevenEighths.CenteredMomentSecondDyadicRowSupport

end

end OAI
