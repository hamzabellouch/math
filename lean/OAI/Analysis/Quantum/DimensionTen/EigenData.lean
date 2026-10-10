import OAI.Analysis.Quantum.DimensionTen.BorderRelations

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma mon_product_0_0 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 0 = low t 3 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_0_0 : B0 *ᵥ Pi.single 0 1 = d • Pi.single 3 1 := by decide +kernel

lemma NB_column_0_0 : NB 0 *ᵥ eQ 0 = eQ 3 :=
  normalize_shift B0 0 3 column_0_0

lemma mon_product_0_1 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 1 = low t 7 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_0_1 : B0 *ᵥ Pi.single 1 1 = d • Pi.single 7 1 := by decide +kernel

lemma NB_column_0_1 : NB 0 *ᵥ eQ 1 = eQ 7 :=
  normalize_shift B0 1 7 column_0_1

lemma mon_product_0_2 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 2 = low t 8 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_0_2 : B0 *ᵥ Pi.single 2 1 = d • Pi.single 8 1 := by decide +kernel

lemma NB_column_0_2 : NB 0 *ᵥ eQ 2 = eQ 8 :=
  normalize_shift B0 2 8 column_0_2

lemma mon_product_0_3 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 3 = low t 9 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_3 : B0 *ᵥ Pi.single 3 1 = d • Pi.single 9 1 := by decide +kernel

lemma NB_column_0_3 : NB 0 *ᵥ eQ 3 = eQ 9 :=
  normalize_shift B0 3 9 column_0_3

lemma mon_product_0_4 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 4 = low t 14 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_0_4 : B0 *ᵥ Pi.single 4 1 = d • Pi.single 14 1 := by decide +kernel

lemma NB_column_0_4 : NB 0 *ᵥ eQ 4 = eQ 14 :=
  normalize_shift B0 4 14 column_0_4

lemma mon_product_0_5 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 5 = low t 15 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_0_5 : B0 *ᵥ Pi.single 5 1 = d • Pi.single 15 1 := by decide +kernel

lemma NB_column_0_5 : NB 0 *ᵥ eQ 5 = eQ 15 :=
  normalize_shift B0 5 15 column_0_5

lemma mon_product_0_6 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 6 = low t 16 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_0_6 : B0 *ᵥ Pi.single 6 1 = d • Pi.single 16 1 := by decide +kernel

lemma NB_column_0_6 : NB 0 *ᵥ eQ 6 = eQ 16 :=
  normalize_shift B0 6 16 column_0_6

lemma mon_product_0_7 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 7 = low t 17 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_7 : B0 *ᵥ Pi.single 7 1 = d • Pi.single 17 1 := by decide +kernel

lemma NB_column_0_7 : NB 0 *ᵥ eQ 7 = eQ 17 :=
  normalize_shift B0 7 17 column_0_7

lemma mon_product_0_8 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 8 = low t 18 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_8 : B0 *ᵥ Pi.single 8 1 = d • Pi.single 18 1 := by decide +kernel

lemma NB_column_0_8 : NB 0 *ᵥ eQ 8 = eQ 18 :=
  normalize_shift B0 8 18 column_0_8

lemma mon_product_0_9 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 9 = low t 19 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_9 : B0 *ᵥ Pi.single 9 1 = d • Pi.single 19 1 := by decide +kernel

lemma NB_column_0_9 : NB 0 *ᵥ eQ 9 = eQ 19 :=
  normalize_shift B0 9 19 column_0_9

lemma mon_product_0_10 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 10 = high t 5 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]

lemma column_0_10 : ∀ m : Fin 20, B0 m 10 = Cnum 5 m := by decide +kernel

lemma NB_column_0_10 : NB 0 *ᵥ eQ 10 = C 5 :=
  normalize_border B0 5 10 column_0_10

lemma mon_product_0_11 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 11 = high t 6 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]

lemma column_0_11 : ∀ m : Fin 20, B0 m 11 = Cnum 6 m := by decide +kernel

lemma NB_column_0_11 : NB 0 *ᵥ eQ 11 = C 6 :=
  normalize_border B0 6 11 column_0_11

lemma mon_product_0_12 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 12 = high t 7 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]

lemma column_0_12 : ∀ m : Fin 20, B0 m 12 = Cnum 7 m := by decide +kernel

lemma NB_column_0_12 : NB 0 *ᵥ eQ 12 = C 7 :=
  normalize_border B0 7 12 column_0_12

lemma mon_product_0_13 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 13 = high t 8 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]

lemma column_0_13 : ∀ m : Fin 20, B0 m 13 = Cnum 8 m := by decide +kernel

lemma NB_column_0_13 : NB 0 *ᵥ eQ 13 = C 8 :=
  normalize_border B0 8 13 column_0_13

lemma mon_product_0_14 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 14 = high t 9 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_14 : ∀ m : Fin 20, B0 m 14 = Cnum 9 m := by decide +kernel

lemma NB_column_0_14 : NB 0 *ᵥ eQ 14 = C 9 :=
  normalize_border B0 9 14 column_0_14

lemma mon_product_0_15 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 15 = high t 10 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_15 : ∀ m : Fin 20, B0 m 15 = Cnum 10 m := by decide +kernel

lemma NB_column_0_15 : NB 0 *ᵥ eQ 15 = C 10 :=
  normalize_border B0 10 15 column_0_15

lemma mon_product_0_16 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 16 = high t 11 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_16 : ∀ m : Fin 20, B0 m 16 = Cnum 11 m := by decide +kernel

lemma NB_column_0_16 : NB 0 *ᵥ eQ 16 = C 11 :=
  normalize_border B0 11 16 column_0_16

lemma mon_product_0_17 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 17 = high t 12 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_17 : ∀ m : Fin 20, B0 m 17 = Cnum 12 m := by decide +kernel

lemma NB_column_0_17 : NB 0 *ᵥ eQ 17 = C 12 :=
  normalize_border B0 12 17 column_0_17

lemma mon_product_0_18 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 18 = high t 13 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_18 : ∀ m : Fin 20, B0 m 18 = Cnum 13 m := by decide +kernel

lemma NB_column_0_18 : NB 0 *ᵥ eQ 18 = C 13 :=
  normalize_border B0 13 18 column_0_18

lemma mon_product_0_19 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 0 * low t 19 = high t 14 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_0_19 : ∀ m : Fin 20, B0 m 19 = Cnum 14 m := by decide +kernel

lemma NB_column_0_19 : NB 0 *ᵥ eQ 19 = C 14 :=
  normalize_border B0 14 19 column_0_19

lemma mon_product_1_0 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 0 = low t 2 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_1_0 : B1 *ᵥ Pi.single 0 1 = d • Pi.single 2 1 := by decide +kernel

lemma NB_column_1_0 : NB 1 *ᵥ eQ 0 = eQ 2 :=
  normalize_shift B1 0 2 column_1_0

lemma mon_product_1_1 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 1 = low t 5 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_1_1 : B1 *ᵥ Pi.single 1 1 = d • Pi.single 5 1 := by decide +kernel

lemma NB_column_1_1 : NB 1 *ᵥ eQ 1 = eQ 5 :=
  normalize_shift B1 1 5 column_1_1

lemma mon_product_1_2 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 2 = low t 6 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_2 : B1 *ᵥ Pi.single 2 1 = d • Pi.single 6 1 := by decide +kernel

lemma NB_column_1_2 : NB 1 *ᵥ eQ 2 = eQ 6 :=
  normalize_shift B1 2 6 column_1_2

lemma mon_product_1_3 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 3 = low t 8 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_3 : B1 *ᵥ Pi.single 3 1 = d • Pi.single 8 1 := by decide +kernel

lemma NB_column_1_3 : NB 1 *ᵥ eQ 3 = eQ 8 :=
  normalize_shift B1 3 8 column_1_3

lemma mon_product_1_4 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 4 = low t 11 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_1_4 : B1 *ᵥ Pi.single 4 1 = d • Pi.single 11 1 := by decide +kernel

lemma NB_column_1_4 : NB 1 *ᵥ eQ 4 = eQ 11 :=
  normalize_shift B1 4 11 column_1_4

lemma mon_product_1_5 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 5 = low t 12 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_5 : B1 *ᵥ Pi.single 5 1 = d • Pi.single 12 1 := by decide +kernel

lemma NB_column_1_5 : NB 1 *ᵥ eQ 5 = eQ 12 :=
  normalize_shift B1 5 12 column_1_5

lemma mon_product_1_6 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 6 = low t 13 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_6 : B1 *ᵥ Pi.single 6 1 = d • Pi.single 13 1 := by decide +kernel

lemma NB_column_1_6 : NB 1 *ᵥ eQ 6 = eQ 13 :=
  normalize_shift B1 6 13 column_1_6

lemma mon_product_1_7 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 7 = low t 15 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_7 : B1 *ᵥ Pi.single 7 1 = d • Pi.single 15 1 := by decide +kernel

lemma NB_column_1_7 : NB 1 *ᵥ eQ 7 = eQ 15 :=
  normalize_shift B1 7 15 column_1_7

lemma mon_product_1_8 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 8 = low t 16 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_8 : B1 *ᵥ Pi.single 8 1 = d • Pi.single 16 1 := by decide +kernel

lemma NB_column_1_8 : NB 1 *ᵥ eQ 8 = eQ 16 :=
  normalize_shift B1 8 16 column_1_8

lemma mon_product_1_9 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 9 = low t 18 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_9 : B1 *ᵥ Pi.single 9 1 = d • Pi.single 18 1 := by decide +kernel

lemma NB_column_1_9 : NB 1 *ᵥ eQ 9 = eQ 18 :=
  normalize_shift B1 9 18 column_1_9

lemma mon_product_1_10 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 10 = high t 1 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]

lemma column_1_10 : ∀ m : Fin 20, B1 m 10 = Cnum 1 m := by decide +kernel

lemma NB_column_1_10 : NB 1 *ᵥ eQ 10 = C 1 :=
  normalize_border B1 1 10 column_1_10

lemma mon_product_1_11 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 11 = high t 2 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_11 : ∀ m : Fin 20, B1 m 11 = Cnum 2 m := by decide +kernel

lemma NB_column_1_11 : NB 1 *ᵥ eQ 11 = C 2 :=
  normalize_border B1 2 11 column_1_11

lemma mon_product_1_12 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 12 = high t 3 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_12 : ∀ m : Fin 20, B1 m 12 = Cnum 3 m := by decide +kernel

lemma NB_column_1_12 : NB 1 *ᵥ eQ 12 = C 3 :=
  normalize_border B1 3 12 column_1_12

lemma mon_product_1_13 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 13 = high t 4 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_13 : ∀ m : Fin 20, B1 m 13 = Cnum 4 m := by decide +kernel

lemma NB_column_1_13 : NB 1 *ᵥ eQ 13 = C 4 :=
  normalize_border B1 4 13 column_1_13

lemma mon_product_1_14 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 14 = high t 6 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_14 : ∀ m : Fin 20, B1 m 14 = Cnum 6 m := by decide +kernel

lemma NB_column_1_14 : NB 1 *ᵥ eQ 14 = C 6 :=
  normalize_border B1 6 14 column_1_14

lemma mon_product_1_15 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 15 = high t 7 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_15 : ∀ m : Fin 20, B1 m 15 = Cnum 7 m := by decide +kernel

lemma NB_column_1_15 : NB 1 *ᵥ eQ 15 = C 7 :=
  normalize_border B1 7 15 column_1_15

lemma mon_product_1_16 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 16 = high t 8 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_16 : ∀ m : Fin 20, B1 m 16 = Cnum 8 m := by decide +kernel

lemma NB_column_1_16 : NB 1 *ᵥ eQ 16 = C 8 :=
  normalize_border B1 8 16 column_1_16

lemma mon_product_1_17 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 17 = high t 10 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_17 : ∀ m : Fin 20, B1 m 17 = Cnum 10 m := by decide +kernel

lemma NB_column_1_17 : NB 1 *ᵥ eQ 17 = C 10 :=
  normalize_border B1 10 17 column_1_17

lemma mon_product_1_18 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 18 = high t 11 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_18 : ∀ m : Fin 20, B1 m 18 = Cnum 11 m := by decide +kernel

lemma NB_column_1_18 : NB 1 *ᵥ eQ 18 = C 11 :=
  normalize_border B1 11 18 column_1_18

lemma mon_product_1_19 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 1 * low t 19 = high t 13 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_1_19 : ∀ m : Fin 20, B1 m 19 = Cnum 13 m := by decide +kernel

lemma NB_column_1_19 : NB 1 *ᵥ eQ 19 = C 13 :=
  normalize_border B1 13 19 column_1_19

lemma mon_product_2_0 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 0 = low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma column_2_0 : B2 *ᵥ Pi.single 0 1 = d • Pi.single 1 1 := by decide +kernel

lemma NB_column_2_0 : NB 2 *ᵥ eQ 0 = eQ 1 :=
  normalize_shift B2 0 1 column_2_0

lemma mon_product_2_1 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 1 = low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_1 : B2 *ᵥ Pi.single 1 1 = d • Pi.single 4 1 := by decide +kernel

lemma NB_column_2_1 : NB 2 *ᵥ eQ 1 = eQ 4 :=
  normalize_shift B2 1 4 column_2_1

lemma mon_product_2_2 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 2 = low t 5 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_2 : B2 *ᵥ Pi.single 2 1 = d • Pi.single 5 1 := by decide +kernel

lemma NB_column_2_2 : NB 2 *ᵥ eQ 2 = eQ 5 :=
  normalize_shift B2 2 5 column_2_2

lemma mon_product_2_3 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 3 = low t 7 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_3 : B2 *ᵥ Pi.single 3 1 = d • Pi.single 7 1 := by decide +kernel

lemma NB_column_2_3 : NB 2 *ᵥ eQ 3 = eQ 7 :=
  normalize_shift B2 3 7 column_2_3

lemma mon_product_2_4 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 4 = low t 10 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_4 : B2 *ᵥ Pi.single 4 1 = d • Pi.single 10 1 := by decide +kernel

lemma NB_column_2_4 : NB 2 *ᵥ eQ 4 = eQ 10 :=
  normalize_shift B2 4 10 column_2_4

lemma mon_product_2_5 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 5 = low t 11 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_5 : B2 *ᵥ Pi.single 5 1 = d • Pi.single 11 1 := by decide +kernel

lemma NB_column_2_5 : NB 2 *ᵥ eQ 5 = eQ 11 :=
  normalize_shift B2 5 11 column_2_5

lemma mon_product_2_6 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 6 = low t 12 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_6 : B2 *ᵥ Pi.single 6 1 = d • Pi.single 12 1 := by decide +kernel

lemma NB_column_2_6 : NB 2 *ᵥ eQ 6 = eQ 12 :=
  normalize_shift B2 6 12 column_2_6

lemma mon_product_2_7 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 7 = low t 14 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_7 : B2 *ᵥ Pi.single 7 1 = d • Pi.single 14 1 := by decide +kernel

lemma NB_column_2_7 : NB 2 *ᵥ eQ 7 = eQ 14 :=
  normalize_shift B2 7 14 column_2_7

lemma mon_product_2_8 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 8 = low t 15 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_8 : B2 *ᵥ Pi.single 8 1 = d • Pi.single 15 1 := by decide +kernel

lemma NB_column_2_8 : NB 2 *ᵥ eQ 8 = eQ 15 :=
  normalize_shift B2 8 15 column_2_8

lemma mon_product_2_9 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 9 = low t 17 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_9 : B2 *ᵥ Pi.single 9 1 = d • Pi.single 17 1 := by decide +kernel

lemma NB_column_2_9 : NB 2 *ᵥ eQ 9 = eQ 17 :=
  normalize_shift B2 9 17 column_2_9

lemma mon_product_2_10 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 10 = high t 0 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_10 : ∀ m : Fin 20, B2 m 10 = Cnum 0 m := by decide +kernel

lemma NB_column_2_10 : NB 2 *ᵥ eQ 10 = C 0 :=
  normalize_border B2 0 10 column_2_10

lemma mon_product_2_11 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 11 = high t 1 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_11 : ∀ m : Fin 20, B2 m 11 = Cnum 1 m := by decide +kernel

lemma NB_column_2_11 : NB 2 *ᵥ eQ 11 = C 1 :=
  normalize_border B2 1 11 column_2_11

lemma mon_product_2_12 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 12 = high t 2 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_12 : ∀ m : Fin 20, B2 m 12 = Cnum 2 m := by decide +kernel

lemma NB_column_2_12 : NB 2 *ᵥ eQ 12 = C 2 :=
  normalize_border B2 2 12 column_2_12

lemma mon_product_2_13 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 13 = high t 3 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_13 : ∀ m : Fin 20, B2 m 13 = Cnum 3 m := by decide +kernel

lemma NB_column_2_13 : NB 2 *ᵥ eQ 13 = C 3 :=
  normalize_border B2 3 13 column_2_13

lemma mon_product_2_14 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 14 = high t 5 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_14 : ∀ m : Fin 20, B2 m 14 = Cnum 5 m := by decide +kernel

lemma NB_column_2_14 : NB 2 *ᵥ eQ 14 = C 5 :=
  normalize_border B2 5 14 column_2_14

lemma mon_product_2_15 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 15 = high t 6 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_15 : ∀ m : Fin 20, B2 m 15 = Cnum 6 m := by decide +kernel

lemma NB_column_2_15 : NB 2 *ᵥ eQ 15 = C 6 :=
  normalize_border B2 6 15 column_2_15

lemma mon_product_2_16 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 16 = high t 7 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_16 : ∀ m : Fin 20, B2 m 16 = Cnum 7 m := by decide +kernel

lemma NB_column_2_16 : NB 2 *ᵥ eQ 16 = C 7 :=
  normalize_border B2 7 16 column_2_16

lemma mon_product_2_17 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 17 = high t 9 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_17 : ∀ m : Fin 20, B2 m 17 = Cnum 9 m := by decide +kernel

lemma NB_column_2_17 : NB 2 *ᵥ eQ 17 = C 9 :=
  normalize_border B2 9 17 column_2_17

lemma mon_product_2_18 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 18 = high t 10 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_18 : ∀ m : Fin 20, B2 m 18 = Cnum 10 m := by decide +kernel

lemma NB_column_2_18 : NB 2 *ᵥ eQ 18 = C 10 :=
  normalize_border B2 10 18 column_2_18

lemma mon_product_2_19 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    t 2 * low t 19 = high t 12 := by
  simp [low, high, mon, monExps, Fin.prod_univ_succ]
  ring

lemma column_2_19 : ∀ m : Fin 20, B2 m 19 = Cnum 12 m := by decide +kernel

lemma NB_column_2_19 : NB 2 *ᵥ eQ 19 = C 12 :=
  normalize_border B2 12 19 column_2_19

lemma single_to_sum {R : Type*} [CommRing R] [Algebra ℚ R]
    (i : Fin 20) (v : Fin 20 → R) :
    ∑ m, (algebraMap ℚ R) (eQ i m) * v m = v i := by
  simp [eQ, Pi.single_apply]

lemma eigen_columns {R : Type*} [CommRing R] [Algebra ℚ R]
    (t : Fin 3 → R) (h : ∀ i, high t i = ∑ m, (algebraMap ℚ R) (C i m) * low t m)
    (j : Fin 3) (k : Fin 20) :
    t j * low t k = ∑ m, (algebraMap ℚ R) (NB j m k) * low t m := by
  have he : (fun m => NB j m k) = NB j *ᵥ eQ k := by
    ext m
    simp only [eQ, Matrix.mulVec_single_one]
    rfl
  change t j * low t k = ∑ m, (algebraMap ℚ R) ((fun m => NB j m k) m) * low t m
  rw [he]
  clear he
  fin_cases j <;> fin_cases k <;> dsimp only
  · erw [mon_product_0_0 t, NB_column_0_0]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_1 t, NB_column_0_1]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_2 t, NB_column_0_2]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_3 t, NB_column_0_3]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_4 t, NB_column_0_4]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_5 t, NB_column_0_5]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_6 t, NB_column_0_6]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_7 t, NB_column_0_7]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_8 t, NB_column_0_8]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_9 t, NB_column_0_9]
    exact (single_to_sum _ _).symm
  · erw [mon_product_0_10 t, NB_column_0_10]
    exact h 5
  · erw [mon_product_0_11 t, NB_column_0_11]
    exact h 6
  · erw [mon_product_0_12 t, NB_column_0_12]
    exact h 7
  · erw [mon_product_0_13 t, NB_column_0_13]
    exact h 8
  · erw [mon_product_0_14 t, NB_column_0_14]
    exact h 9
  · erw [mon_product_0_15 t, NB_column_0_15]
    exact h 10
  · erw [mon_product_0_16 t, NB_column_0_16]
    exact h 11
  · erw [mon_product_0_17 t, NB_column_0_17]
    exact h 12
  · erw [mon_product_0_18 t, NB_column_0_18]
    exact h 13
  · erw [mon_product_0_19 t, NB_column_0_19]
    exact h 14
  · erw [mon_product_1_0 t, NB_column_1_0]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_1 t, NB_column_1_1]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_2 t, NB_column_1_2]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_3 t, NB_column_1_3]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_4 t, NB_column_1_4]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_5 t, NB_column_1_5]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_6 t, NB_column_1_6]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_7 t, NB_column_1_7]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_8 t, NB_column_1_8]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_9 t, NB_column_1_9]
    exact (single_to_sum _ _).symm
  · erw [mon_product_1_10 t, NB_column_1_10]
    exact h 1
  · erw [mon_product_1_11 t, NB_column_1_11]
    exact h 2
  · erw [mon_product_1_12 t, NB_column_1_12]
    exact h 3
  · erw [mon_product_1_13 t, NB_column_1_13]
    exact h 4
  · erw [mon_product_1_14 t, NB_column_1_14]
    exact h 6
  · erw [mon_product_1_15 t, NB_column_1_15]
    exact h 7
  · erw [mon_product_1_16 t, NB_column_1_16]
    exact h 8
  · erw [mon_product_1_17 t, NB_column_1_17]
    exact h 10
  · erw [mon_product_1_18 t, NB_column_1_18]
    exact h 11
  · erw [mon_product_1_19 t, NB_column_1_19]
    exact h 13
  · erw [mon_product_2_0 t, NB_column_2_0]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_1 t, NB_column_2_1]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_2 t, NB_column_2_2]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_3 t, NB_column_2_3]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_4 t, NB_column_2_4]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_5 t, NB_column_2_5]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_6 t, NB_column_2_6]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_7 t, NB_column_2_7]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_8 t, NB_column_2_8]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_9 t, NB_column_2_9]
    exact (single_to_sum _ _).symm
  · erw [mon_product_2_10 t, NB_column_2_10]
    exact h 0
  · erw [mon_product_2_11 t, NB_column_2_11]
    exact h 1
  · erw [mon_product_2_12 t, NB_column_2_12]
    exact h 2
  · erw [mon_product_2_13 t, NB_column_2_13]
    exact h 3
  · erw [mon_product_2_14 t, NB_column_2_14]
    exact h 5
  · erw [mon_product_2_15 t, NB_column_2_15]
    exact h 6
  · erw [mon_product_2_16 t, NB_column_2_16]
    exact h 7
  · erw [mon_product_2_17 t, NB_column_2_17]
    exact h 9
  · erw [mon_product_2_18 t, NB_column_2_18]
    exact h 10
  · erw [mon_product_2_19 t, NB_column_2_19]
    exact h 12

end DimensionTen.Border

end
end

end OAI
