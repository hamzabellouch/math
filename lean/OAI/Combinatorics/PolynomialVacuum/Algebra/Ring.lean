import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialScalars

namespace OAI

namespace PolynomialVacuumAlgebra
syntax "vacuum_ring_finish" : tactic
macro_rules
  | `(tactic| vacuum_ring_finish) => `(tactic|
    solve
    | (try ring_nf
       all_goals try simp only [q_inv]
       all_goals try ring_nf
       all_goals try simp only [q_pow_eight,q_pow_9,q_pow_10,q_pow_11,q_pow_12,q_pow_13,q_pow_14,q_pow_15,q_pow_16,q_pow_17,q_pow_18,q_pow_19,q_pow_20,q_pow_21,q_pow_22,q_pow_23,q_pow_24,q_pow_25,q_pow_26,q_pow_27,q_pow_28,q_pow_29,q_pow_30,q_pow_31,q_pow_32,q_pow_33,q_pow_34,q_pow_35,q_pow_36,q_pow_37,q_pow_38,q_pow_39,q_pow_40,q_pow_41,q_pow_42,q_pow_43,q_pow_44,q_pow_45,q_pow_46,q_pow_47,q_pow_48,q_pow_49,q_pow_50,q_pow_51,q_pow_52,q_pow_53,q_pow_54,q_pow_55,q_pow_56,q_pow_57,q_pow_58,q_pow_59,q_pow_60,q_pow_61,q_pow_62,q_pow_63,q_pow_64]
       all_goals ring)
    | (apply Or.inl
       vacuum_ring_finish)
    | (apply Or.inr
       vacuum_ring_finish))
end PolynomialVacuumAlgebra

end OAI
