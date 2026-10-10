import OAI.Combinatorics.SnakyCertificate.Lists

namespace OAI

namespace SnakyCertificate.Check

def cache_320_A_part0 : List Cell := [(0, -3), (0, -2), (1, -3), (1, 0), (3, 0)]

def cache_320_A : List Cell := cache_320_A_part0

def cache_320_H_part0 : List Cell := [(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0)]

def cache_320_H_part1 : List Cell := [(4, 1), (5, 0), (5, 1), (6, 1)]

def cache_320_H : List Cell := (cache_320_H_part0 ++ cache_320_H_part1)

def cache_320 : ListRow := ⟨cache_320_A, cache_320_H, 9⟩

def cache_321_A_part0 : List Cell := [(0, 1), (0, 2), (1, 1), (2, 1)]

def cache_321_A : List Cell := cache_321_A_part0

def cache_321_H_part0 : List Cell := [(-3, 3), (-2, 3), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (3, 1)]

def cache_321_H_part1 : List Cell := [(3, 2), (4, 1), (4, 2), (5, 2)]

def cache_321_H : List Cell := (cache_321_H_part0 ++ cache_321_H_part1)

def cache_321 : ListRow := ⟨cache_321_A, cache_321_H, 8⟩

def cache_322_A_part0 : List Cell := [(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)]

def cache_322_A : List Cell := cache_322_A_part0

def cache_322_H_part0 : List Cell := [(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4)]

def cache_322_H_part1 : List Cell := [(2, -2), (2, -1), (2, 0), (2, 1)]

def cache_322_H : List Cell := (cache_322_H_part0 ++ cache_322_H_part1)

def cache_322 : ListRow := ⟨cache_322_A, cache_322_H, 9⟩

def cache_323_A_part0 : List Cell := [(-2, 0), (-1, -2), (-1, -1), (-1, 0)]

def cache_323_A : List Cell := cache_323_A_part0

def cache_323_H_part0 : List Cell := [(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)]

def cache_323_H_part1 : List Cell := [(3, -1), (3, 0), (3, 1), (4, -1)]

def cache_323_H : List Cell := (cache_323_H_part0 ++ cache_323_H_part1)

def cache_323 : ListRow := ⟨cache_323_A, cache_323_H, 8⟩

def cache_324_A_part0 : List Cell := [(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)]

def cache_324_A : List Cell := cache_324_A_part0

def cache_324_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_324_H_part1 : List Cell := [(5, -1), (5, 0), (5, 1), (6, -1)]

def cache_324_H : List Cell := (cache_324_H_part0 ++ cache_324_H_part1)

def cache_324 : ListRow := ⟨cache_324_A, cache_324_H, 9⟩

def cache_325_A_part0 : List Cell := [(-1, 0), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_325_A : List Cell := cache_325_A_part0

def cache_325_H_part0 : List Cell := [(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_325_H_part1 : List Cell := [(5, -1), (5, 0), (5, 1), (6, 1)]

def cache_325_H : List Cell := (cache_325_H_part0 ++ cache_325_H_part1)

def cache_325 : ListRow := ⟨cache_325_A, cache_325_H, 8⟩

def cache_326_A_part0 : List Cell := [(-4, -3), (-3, 0), (-2, 0), (-1, 0)]

def cache_326_A : List Cell := cache_326_A_part0

def cache_326_H_part0 : List Cell := [(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1)]

def cache_326_H_part1 : List Cell := [(1, 0), (1, 1), (2, -1), (2, 1)]

def cache_326_H : List Cell := (cache_326_H_part0 ++ cache_326_H_part1)

def cache_326 : ListRow := ⟨cache_326_A, cache_326_H, 10⟩

def cache_327_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, -1), (1, 0)]

def cache_327_A : List Cell := cache_327_A_part0

def cache_327_H_part0 : List Cell := [(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0)]

def cache_327_H_part1 : List Cell := [(4, 1), (5, -1), (5, 0), (5, 1), (6, -1)]

def cache_327_H : List Cell := (cache_327_H_part0 ++ cache_327_H_part1)

def cache_327 : ListRow := ⟨cache_327_A, cache_327_H, 8⟩

def cache_328_A_part0 : List Cell := [(-1, -3), (0, -3), (0, -2), (0, -1)]

def cache_328_A : List Cell := cache_328_A_part0

def cache_328_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0)]

def cache_328_H_part1 : List Cell := [(3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_328_H : List Cell := (cache_328_H_part0 ++ cache_328_H_part1)

def cache_328 : ListRow := ⟨cache_328_A, cache_328_H, 10⟩

def cache_329_A_part0 : List Cell := [(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)]

def cache_329_A : List Cell := cache_329_A_part0

def cache_329_H_part0 : List Cell := [(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)]

def cache_329_H_part1 : List Cell := [(3, 2), (4, 0), (4, 1), (4, 2), (5, 0)]

def cache_329_H : List Cell := (cache_329_H_part0 ++ cache_329_H_part1)

def cache_329 : ListRow := ⟨cache_329_A, cache_329_H, 9⟩

def cache_330_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0)]

def cache_330_A : List Cell := cache_330_A_part0

def cache_330_H_part0 : List Cell := [(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1)]

def cache_330_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (3, 1), (3, 2)]

def cache_330_H : List Cell := (cache_330_H_part0 ++ cache_330_H_part1)

def cache_330 : ListRow := ⟨cache_330_A, cache_330_H, 10⟩

def cache_331_A_part0 : List Cell := [(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, 1)]

def cache_331_A : List Cell := cache_331_A_part0

def cache_331_H_part0 : List Cell := [(-7, 0), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2)]

def cache_331_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (3, 0), (3, 2)]

def cache_331_H : List Cell := (cache_331_H_part0 ++ cache_331_H_part1)

def cache_331 : ListRow := ⟨cache_331_A, cache_331_H, 9⟩

def cache_332_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -1), (1, 0)]

def cache_332_A : List Cell := cache_332_A_part0

def cache_332_H_part0 : List Cell := [(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3)]

def cache_332_H_part1 : List Cell := [(4, -2), (5, -4), (5, -3), (5, -2), (6, -2)]

def cache_332_H : List Cell := (cache_332_H_part0 ++ cache_332_H_part1)

def cache_332 : ListRow := ⟨cache_332_A, cache_332_H, 10⟩

def cache_333_A_part0 : List Cell := [(0, -3), (0, -2), (1, -4), (1, -3), (1, -2), (2, 0)]

def cache_333_A : List Cell := cache_333_A_part0

def cache_333_H_part0 : List Cell := [(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_333_H_part1 : List Cell := [(5, 0), (5, 1), (6, -1), (6, 0), (6, 1)]

def cache_333_H : List Cell := (cache_333_H_part0 ++ cache_333_H_part1)

def cache_333 : ListRow := ⟨cache_333_A, cache_333_H, 10⟩

def cache_334_A_part0 : List Cell := [(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)]

def cache_334_A : List Cell := cache_334_A_part0

def cache_334_H_part0 : List Cell := [(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1)]

def cache_334_H_part1 : List Cell := [(4, 2), (5, 0), (5, 1), (5, 2), (6, 0)]

def cache_334_H : List Cell := (cache_334_H_part0 ++ cache_334_H_part1)

def cache_334 : ListRow := ⟨cache_334_A, cache_334_H, 10⟩

def cache_335_A_part0 : List Cell := [(-3, 0), (-2, -2), (-2, 0), (-1, -1), (-1, 0)]

def cache_335_A : List Cell := cache_335_A_part0

def cache_335_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1)]

def cache_335_H_part1 : List Cell := [(2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_335_H : List Cell := (cache_335_H_part0 ++ cache_335_H_part1)

def cache_335 : ListRow := ⟨cache_335_A, cache_335_H, 9⟩

def cache_336_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, 0)]

def cache_336_A : List Cell := cache_336_A_part0

def cache_336_H_part0 : List Cell := [(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0)]

def cache_336_H_part1 : List Cell := [(3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)]

def cache_336_H : List Cell := (cache_336_H_part0 ++ cache_336_H_part1)

def cache_336 : ListRow := ⟨cache_336_A, cache_336_H, 9⟩

def cache_337_A_part0 : List Cell := [(-3, 0), (-1, 0), (-1, 1), (-1, 2)]

def cache_337_A : List Cell := cache_337_A_part0

def cache_337_H_part0 : List Cell := [(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]

def cache_337_H_part1 : List Cell := [(2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_337_H : List Cell := (cache_337_H_part0 ++ cache_337_H_part1)

def cache_337 : ListRow := ⟨cache_337_A, cache_337_H, 9⟩

def cache_338_A_part0 : List Cell := [(-1, 0), (1, -2), (1, -1), (1, 0)]

def cache_338_A : List Cell := cache_338_A_part0

def cache_338_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1)]

def cache_338_H_part1 : List Cell := [(4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)]

def cache_338_H : List Cell := (cache_338_H_part0 ++ cache_338_H_part1)

def cache_338 : ListRow := ⟨cache_338_A, cache_338_H, 8⟩

def cache_339_A_part0 : List Cell := [(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)]

def cache_339_A : List Cell := cache_339_A_part0

def cache_339_H_part0 : List Cell := [(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, -1)]

def cache_339_H_part1 : List Cell := [(3, 0), (4, -4), (4, -2), (4, -1), (4, 0), (4, 1)]

def cache_339_H : List Cell := (cache_339_H_part0 ++ cache_339_H_part1)

def cache_339 : ListRow := ⟨cache_339_A, cache_339_H, 10⟩

def cache_340_A_part0 : List Cell := [(-1, 1), (0, -1), (0, 1)]

def cache_340_A : List Cell := cache_340_A_part0

def cache_340_H_part0 : List Cell := [(-4, -2), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0)]

def cache_340_H_part1 : List Cell := [(1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0)]

def cache_340_H : List Cell := (cache_340_H_part0 ++ cache_340_H_part1)

def cache_340 : ListRow := ⟨cache_340_A, cache_340_H, 10⟩

def cache_341_A_part0 : List Cell := [(-3, 0), (-2, 0), (-1, 0), (-1, 1)]

def cache_341_A : List Cell := cache_341_A_part0

def cache_341_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)]

def cache_341_H_part1 : List Cell := [(2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)]

def cache_341_H : List Cell := (cache_341_H_part0 ++ cache_341_H_part1)

def cache_341 : ListRow := ⟨cache_341_A, cache_341_H, 9⟩

def cache_342_A_part0 : List Cell := [(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2)]

def cache_342_A : List Cell := cache_342_A_part0

def cache_342_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1)]

def cache_342_H_part1 : List Cell := [(2, -3), (2, -2), (2, -1), (3, -3), (3, -2), (3, -1)]

def cache_342_H : List Cell := (cache_342_H_part0 ++ cache_342_H_part1)

def cache_342 : ListRow := ⟨cache_342_A, cache_342_H, 9⟩

def cache_343_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)]

def cache_343_A : List Cell := cache_343_A_part0

def cache_343_H_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)]

def cache_343_H : List Cell := cache_343_H_part0

def cache_343 : ListRow := ⟨cache_343_A, cache_343_H, 9⟩

def cache_344_A_part0 : List Cell := [(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (2, -3), (3, -3), (3, -2)]

def cache_344_A : List Cell := cache_344_A_part0

def cache_344_H_part0 : List Cell := [(-1, -1), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3)]

def cache_344_H_part1 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)]

def cache_344_H : List Cell := (cache_344_H_part0 ++ cache_344_H_part1)

def cache_344 : ListRow := ⟨cache_344_A, cache_344_H, 10⟩

def cache_345_A_part0 : List Cell := [(-3, 0), (-3, 3), (-2, 0), (-1, 0), (-1, 3), (0, 1)]

def cache_345_A : List Cell := cache_345_A_part0

def cache_345_H_part0 : List Cell := [(-6, 4), (-5, 3), (-5, 4), (-4, 3), (-4, 4), (-3, 0), (-3, 3), (-3, 4), (-2, 0), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4)]

def cache_345_H_part1 : List Cell := [(1, 5), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4)]

def cache_345_H : List Cell := (cache_345_H_part0 ++ cache_345_H_part1)

def cache_345 : ListRow := ⟨cache_345_A, cache_345_H, 10⟩

def cache_346_A_part0 : List Cell := [(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-1, -3), (0, -3), (0, -2)]

def cache_346_A : List Cell := cache_346_A_part0

def cache_346_H_part0 : List Cell := [(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1)]

def cache_346_H_part1 : List Cell := [(0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_346_H : List Cell := (cache_346_H_part0 ++ cache_346_H_part1)

def cache_346 : ListRow := ⟨cache_346_A, cache_346_H, 10⟩

def cache_347_A_part0 : List Cell := [(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)]

def cache_347_A : List Cell := cache_347_A_part0

def cache_347_H_part0 : List Cell := [(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 1), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2)]

def cache_347_H_part1 : List Cell := [(4, 3), (4, 4), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5)]

def cache_347_H : List Cell := (cache_347_H_part0 ++ cache_347_H_part1)

def cache_347 : ListRow := ⟨cache_347_A, cache_347_H, 11⟩

def cache_348_A_part0 : List Cell := [(-2, 0), (-2, 1), (-1, -1), (0, -2), (0, -1), (1, -1), (1, 0)]

def cache_348_A : List Cell := cache_348_A_part0

def cache_348_H_part0 : List Cell := [(-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, -2)]

def cache_348_H_part1 : List Cell := [(3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]

def cache_348_H : List Cell := (cache_348_H_part0 ++ cache_348_H_part1)

def cache_348 : ListRow := ⟨cache_348_A, cache_348_H, 11⟩

def cache_349_A_part0 : List Cell := [(-1, -3), (-1, -2), (-1, -1), (0, -1)]

def cache_349_A : List Cell := cache_349_A_part0

def cache_349_H_part0 : List Cell := [(-4, 0), (-3, 0), (-2, -4), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2)]

def cache_349_H_part1 : List Cell := [(3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)]

def cache_349_H : List Cell := (cache_349_H_part0 ++ cache_349_H_part1)

def cache_349 : ListRow := ⟨cache_349_A, cache_349_H, 11⟩

def cache_350_A_part0 : List Cell := [(-1, 0), (-1, 1), (1, 0), (1, 2)]

def cache_350_A : List Cell := cache_350_A_part0

def cache_350_H_part0 : List Cell := [(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 3)]

def cache_350_H_part1 : List Cell := [(2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)]

def cache_350_H : List Cell := (cache_350_H_part0 ++ cache_350_H_part1)

def cache_350 : ListRow := ⟨cache_350_A, cache_350_H, 8⟩

def cache_351_A_part0 : List Cell := [(-2, -1), (-2, 0), (-2, 1), (-1, 0)]

def cache_351_A : List Cell := cache_351_A_part0

def cache_351_H_part0 : List Cell := [(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2)]

def cache_351_H_part1 : List Cell := [(1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)]

def cache_351_H : List Cell := (cache_351_H_part0 ++ cache_351_H_part1)

def cache_351 : ListRow := ⟨cache_351_A, cache_351_H, 11⟩

def cache_352_A_part0 : List Cell := [(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2), (3, -1)]

def cache_352_A : List Cell := cache_352_A_part0

def cache_352_H_part0 : List Cell := [(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2)]

def cache_352_H_part1 : List Cell := [(3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]

def cache_352_H : List Cell := (cache_352_H_part0 ++ cache_352_H_part1)

def cache_352 : ListRow := ⟨cache_352_A, cache_352_H, 11⟩

def cache_353_A_part0 : List Cell := [(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)]

def cache_353_A : List Cell := cache_353_A_part0

def cache_353_H_part0 : List Cell := [(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0)]

def cache_353_H_part1 : List Cell := [(1, 1), (1, 2), (1, 3), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4)]

def cache_353_H : List Cell := (cache_353_H_part0 ++ cache_353_H_part1)

def cache_353 : ListRow := ⟨cache_353_A, cache_353_H, 12⟩

def cache_354_A_part0 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, 1), (1, -2)]

def cache_354_A : List Cell := cache_354_A_part0

def cache_354_H_part0 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0)]

def cache_354_H_part1 : List Cell := [(2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0)]

def cache_354_H : List Cell := (cache_354_H_part0 ++ cache_354_H_part1)

def cache_354 : ListRow := ⟨cache_354_A, cache_354_H, 11⟩

def cache_355_A_part0 : List Cell := [(1, -1), (1, 0), (2, -1), (2, 0)]

def cache_355_A : List Cell := cache_355_A_part0

def cache_355_H_part0 : List Cell := [(-2, 0), (-2, 1), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1)]

def cache_355_H_part1 : List Cell := [(3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)]

def cache_355_H : List Cell := (cache_355_H_part0 ++ cache_355_H_part1)

def cache_355 : ListRow := ⟨cache_355_A, cache_355_H, 10⟩

def cache_356_A_part0 : List Cell := [(-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)]

def cache_356_A : List Cell := cache_356_A_part0

def cache_356_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)]

def cache_356_H : List Cell := cache_356_H_part0

def cache_356 : ListRow := ⟨cache_356_A, cache_356_H, 8⟩

def cache_357_A_part0 : List Cell := [(-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 2)]

def cache_357_A : List Cell := cache_357_A_part0

def cache_357_H_part0 : List Cell := [(-4, -1), (-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

def cache_357_H_part1 : List Cell := [(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 3)]

def cache_357_H : List Cell := (cache_357_H_part0 ++ cache_357_H_part1)

def cache_357 : ListRow := ⟨cache_357_A, cache_357_H, 10⟩

def cache_358_A_part0 : List Cell := [(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)]

def cache_358_A : List Cell := cache_358_A_part0

def cache_358_H_part0 : List Cell := [(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0)]

def cache_358_H_part1 : List Cell := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)]

def cache_358_H : List Cell := (cache_358_H_part0 ++ cache_358_H_part1)

def cache_358 : ListRow := ⟨cache_358_A, cache_358_H, 11⟩

def cache_359_A_part0 : List Cell := [(-1, -1), (-1, 1), (0, -1), (0, 1)]

def cache_359_A : List Cell := cache_359_A_part0

def cache_359_H_part0 : List Cell := [(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0)]

def cache_359_H_part1 : List Cell := [(2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)]

def cache_359_H : List Cell := (cache_359_H_part0 ++ cache_359_H_part1)

def cache_359 : ListRow := ⟨cache_359_A, cache_359_H, 9⟩

end SnakyCertificate.Check

end OAI
